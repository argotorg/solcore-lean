import Solcore.Test.Syntax.ExpressionAtoms
import Solcore.Syntax.Parser.Internal.ExpressionAtomTrace
import Solcore.Syntax.Parser.Internal.LambdaTrace
import Solcore.Syntax.Parser.Internal.PostfixTrace
import Solcore.Syntax.Validity
import Solcore.Syntax.Parser.Internal.ExpressionTotality
import Solcore.Syntax.Parser.Internal.BlockTrace
import Solcore.Syntax.Parser.Internal.ExpressionProofs
import Solcore.Syntax.Parser.Internal.PatternProofs
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Syntax.Parser.Internal.DiagnosticTrace
import Solcore.Syntax.Internal.TraceBasics
import Solcore.Syntax.Internal.BlockTrace

/-!
# Expression and pattern tests

Expression layers above the atoms: postfix tails, unary, associative and conditional forms, with
their fuel contracts, and the pattern grammar.
-/

section
-- leanmerge: from Solcore.Test.SyntaxExpressionUnaryTraceSupport
/-! Concrete unary consumers use the real literal child and one supplied
always-rejecting block. All-input postfix completeness is discharged from
exact independent outcomes, soundness, and bounded child execution; no general
recursive expression or block completeness is assumed. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionUnaryTraceSupport

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals ExpressionInternals SyntaxExpressionAtomTotalityProperties

def blockFailure : Failure := {
  span := { source := { origin := .main, path := "unused-unary-block.sol" }, startByte := 0, endByte := 0 }
  found := none, expected := { head := .symbol .leftBrace, tail := [] }, context := .expression
}
def blockParser : Parser Block := fun input => .reject blockFailure input
def blockTrace (_ : SourceId) (_ : Nat) (_ : Remainder) (_ : Block) (_ : Remainder)
    (_ : List ParseDiagnostic) : Prop := False
def blockRejects (_ : SourceId) (_ : Nat) (input rejected : Remainder) (report : ParseDiagnostic)
    (trace : List ParseDiagnostic) : Prop := rejected = input ∧ report = blockFailure.toDiagnostic ∧ trace = []

private theorem block_contract (fuel : Nat) : UnrestrictedFuelElementContract blockParser fuel where
  endIndexOnSuccess result := by contradiction
  cursorLtOnSuccess result := by contradiction
  ordinary input _ := .inr ⟨blockFailure, input, rfl⟩

private theorem block_success_sound : ParserTraceSuccessSound blockParser blockTrace := by
  intro input output value result
  contradiction
private theorem block_reject_sound : ParserTraceRejectSound blockParser blockRejects := by
  intro input rejected failure result
  change Reply.reject blockFailure input = Reply.reject failure rejected at result
  cases result
  exact ⟨[], ⟨rfl, rfl, rfl⟩, by simp⟩
private theorem block_context : ParserSuccessContext blockParser := by
  intro input output value result
  contradiction
private theorem block_reject_frame {input rejected : State} {failure : Failure}
    (result : blockParser input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  change Reply.reject blockFailure input = Reply.reject failure rejected at result
  cases result
  exact ⟨rfl, rfl⟩
private theorem block_outcomes (source : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec blockTrace blockRejects source endByte where
  successResultUnique impossible := False.elim impossible
  rejectResultUnique left right := ⟨left.1.trans right.1.symm, left.2.1.trans right.2.1.symm, left.2.2.trans right.2.2.symm⟩
  successRejectDisjoint _ parsed := by rcases parsed with ⟨_, _, _, impossible⟩; exact impossible

abbrev postfixTrace := ExpressionPostfixLayerTraceParses
  LiteralExpressionTraceParses LiteralExpressionTraceRejects blockTrace blockRejects
abbrev postfixRejects := ExpressionPostfixLayerTraceRejects
  LiteralExpressionTraceParses LiteralExpressionTraceRejects blockTrace blockRejects

private theorem postfix_sound : ParserTraceSuccessSound (expressionPostfix literalExpression blockParser) postfixTrace :=
  expressionPostfix_layer_trace_success_sound literalExpression_trace_success_sound literalExpression_trace_reject_sound
    literalExpression_success_context block_success_sound block_reject_sound block_context
    literalExpression_reject_context block_reject_frame
private theorem postfix_reject_sound : ParserTraceRejectSound (expressionPostfix literalExpression blockParser) postfixRejects :=
  expressionPostfix_layer_reject_trace_sound literalExpression_trace_success_sound literalExpression_trace_reject_sound
    literalExpression_success_context block_success_sound block_reject_sound block_context
    literalExpression_reject_context block_reject_frame
private theorem postfix_ne_invariant (input : State) (error : ParserInvariantError) :
    expressionPostfix literalExpression blockParser input ≠ .invariant error :=
  expressionPostfix_ne_invariant_of_unrestrictedChildFuels literalExpression blockParser
    input.remainingCount input.remainingCount (literal_child_contract _) (block_contract _)
    (fun result => congrArg TokenWindow.endIndex (literalExpression_reject_context result).2)
    (fun result => congrArg TokenWindow.endIndex (block_reject_frame result).2)
    input (Nat.lt_succ_self _) (Nat.lt_succ_self _) error
private theorem postfix_outcomes (source : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec postfixTrace postfixRejects source endByte :=
  expressionPostfixLayerTraceExactOutcomeSpec
    (literalExpressionTraceExactOutcomeSpec source endByte).toTraceExactOutcomeSpec (block_outcomes source endByte)
private theorem postfix_complete : ParserTraceSuccessComplete (expressionPostfix literalExpression blockParser) postfixTrace := by
  intro input value after trace parsed
  exact trace_success_exists_ok_of_sound postfix_sound postfix_reject_sound (postfix_outcomes _ _)
    (postfix_ne_invariant input) parsed
private theorem postfix_reject_complete : ParserTraceRejectComplete (expressionPostfix literalExpression blockParser) postfixRejects := by
  intro input after report trace rejection
  exact trace_reject_exists_reject_of_sound postfix_sound postfix_reject_sound (postfix_outcomes _ _)
    (postfix_ne_invariant input) rejection

private theorem atom_context : ParserSuccessContext (expressionAtom literalExpression blockParser) :=
  expressionAtom_layer_success_context literalExpression_success_context block_context
    literalExpression_reject_context block_reject_frame
private theorem atom_reject_frame {input rejected : State} {failure : Failure}
    (result : expressionAtom literalExpression blockParser input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte :=
  expressionAtom_reject_source_end
    (expressionAtomCore_reject_source_endByte literalExpression_success_context
      (fun result => ⟨(literalExpression_reject_context result).1,
        congrArg TokenWindow.endByte (literalExpression_reject_context result).2⟩)
      (fun result => ⟨(block_reject_frame result).1, congrArg TokenWindow.endByte (block_reject_frame result).2⟩)) result

theorem success_of_trace {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : ExpressionUnaryTraceParses postfixTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    expressionUnary literalExpression blockParser input = .ok value (input.traceResult after trace) :=
  (expressionUnary_trace_success_state_iff postfix_sound postfix_complete
    (fun result => ⟨(expressionPostfix_trace_success_context atom_context literalExpression_success_context result).1,
      congrArg TokenWindow.endByte (expressionPostfix_trace_success_context atom_context literalExpression_success_context result).2⟩)).mp parsed

theorem reject_of_trace {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic}
    (rejection : ExpressionUnaryTraceRejects postfixRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace) :
    expressionUnary literalExpression blockParser input = .reject failure (input.traceResult after trace) :=
  (expressionUnary_trace_reject_failure_state_iff postfix_reject_sound postfix_reject_complete
    (expressionPostfix_reject_context_of_windowProjection atom_context literalExpression_success_context atom_reject_frame
      (fun result => ⟨(literalExpression_reject_context result).1,
        congrArg TokenWindow.endByte (literalExpression_reject_context result).2⟩))).mp rejection

end Solcore.Test.SyntaxExpressionUnaryTraceSupport
end

section
-- leanmerge: from Solcore.Test.SyntaxExpressionUnaryTraceProperties
/-! Canonical prefix order, complete postfix operands, and silent scanner
boundaries are consumed in the reverse direction from independent judgments.
The actual block is the explicitly supplied rejecting test leaf, not a general
recursive block parser. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionUnaryTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals ExpressionInternals SyntaxExpressionUnaryTraceSupport

private def source : SourceId := { origin := .main, path := "unary-trace.sol" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def sym (first last : Nat) (kind : Symbol) : Token := { span := span first last, value := .symbol kind }
private def name : Identifier := { span := span 2 5, value := "a-b" }
private def nameValue : Expr := { span := name.span, value := .identifier name }
private def nameEvent : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def one : Expr := { span := span 6 7, value := .literal { span := span 6 7, value := .decimal "1" } }
private def args : DelimitedList Expr := { span := span 5 8, elements := [one] }
private def callValue : Expr := postfixCallTraceValue nameValue args
private def fieldName : Identifier := { span := span 9 10, value := "c" }
private def fieldValue : Expr := postfixFieldTraceValue callValue (span 8 9) fieldName
private def operators : List (Located UnaryOp) := [⟨span 0 1, .logicalNot⟩, ⟨span 1 2, .bitNot⟩]
private def wrapped : Expr := DeclarativeGrammar.applyUnaryOperators operators fieldValue
private def tokens (suffix : List Token) : List Token :=
  [sym 0 1 .bang, sym 1 2 .tilde, { span := name.span, value := .identifier name.value },
    sym 5 6 .leftParen, { span := span 6 7, value := .decimalLiteral "1" }, sym 7 8 .rightParen] ++ suffix
private def rem (suffix : List Token) (cursor : Nat) : Remainder :=
  { tokens := (tokens suffix).toArray, endIndex := (tokens suffix).length, cursor }
private def state (suffix : List Token) (cursor : Nat) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := (tokens suffix).toArray, cursor
  window := { endIndex := (tokens suffix).length, endByte := 99 }, diagnosticsRev := prior.reverse
}

private theorem prefix_trace (suffix : List Token) : UnaryOperatorsParses (rem suffix 0) operators (rem suffix 2) :=
  .next (afterOperator := rem suffix 1) ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
    (.next ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
      (.done (by simp [UnaryOperatorAbsentAt, TokenKindAbsentAt, TokenAt, rem, tokens])))

private theorem atom_name (suffix : List Token) :
    ExpressionAtomLayerTraceParses LiteralExpressionTraceParses LiteralExpressionTraceRejects blockTrace blockRejects
      source 99 (rem suffix 2) nameValue (rem suffix 3) [nameEvent] := by
  apply ExpressionAtomTraceParses.core
  apply ExpressionAtomDispatchTraceParses.selected .name
  · exact .name (by simp [CoreLiteralStartsAt, TokenAt, rem, tokens])
      (.inr (.inr ⟨name.span, name.value, ⟨by simp [rem, tokens], rfl⟩⟩))
  · exact .parsed (.identifier (by simp [BooleanPatternAbsentAt, TokenKindAbsentAt, TokenAt, rem, tokens])
      (.parsed ⟨⟨by simp [rem, tokens], rfl⟩, rfl, rfl, rfl⟩
        (.hyphen (by unfold IdentifierHyphenSpelling name; decide))))

private theorem arguments_trace (suffix : List Token) :
    NoTrailingDelimitedListTraceParses .leftParen .rightParen true LiteralExpressionTraceParses source 99
      (rem suffix 3) args (rem suffix 6) [] := by
  apply NoTrailingDelimitedListTraceParses.nonempty (afterOpening := rem suffix 4) (afterFirst := rem suffix 5)
    (first := one) (rest := []) (firstEvents := []) (tailEvents := []) (span 5 6) (span 7 8)
  · exact ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
  · exact .absent (by simp [TokenKindAbsentAt, TokenAt, rem, tokens])
  · exact ⟨.parsed (.decimal ⟨by simp [rem, tokens], rfl⟩), rfl⟩
  · change 4 < 5; decide
  · exact .close (by simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym])
      ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩

private def successSuffix : List Token :=
  [sym 8 9 .dot, { span := fieldName.span, value := .identifier fieldName.value }, sym 10 11 .semicolon]
private def successState (prior : List ParseDiagnostic) : State :=
  { state successSuffix 8 prior with diagnosticsRev := nameEvent :: prior.reverse }

private theorem success_trace : ExpressionUnaryTraceParses postfixTrace source 99
    (rem successSuffix 0) wrapped (rem successSuffix 8) [nameEvent] := by
  apply ExpressionUnaryTraceParses.parsed (prefix_trace successSuffix)
  apply ExpressionPostfixTraceParses.parsed (tailEvents := []) (atom_name successSuffix)
  apply PostfixTailTraceParses.call (afterArguments := rem successSuffix 6) (argumentEvents := []) (tailEvents := [])
  · simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym]
  · exact arguments_trace successSuffix
  · apply PostfixTailTraceParses.field (afterDot := rem successSuffix 7) (afterName := rem successSuffix 8)
      (nameEvents := []) (tailEvents := []) (span 8 9)
    · simp [TokenKindAbsentAt, TokenAt, rem, tokens, successSuffix, sym]
    · simp [TokenKindAbsentAt, TokenAt, rem, tokens, successSuffix, sym]
    · exact ⟨⟨by decide, rfl⟩, rfl⟩
    · exact .parsed ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩ (.clean (by unfold IdentifierHyphenSpelling fieldName; decide))
    · exact .done (by simp [PostfixSuffixAbsentAt, TokenKindAbsentAt, TokenAt, rem, tokens, successSuffix, sym])

/-- Bang is outermost and tilde wraps the complete call/field operand. Exactly
one checked-name event follows all prior diagnostics; the semicolon is unread. -/
theorem source_order_prefix_wraps_maximal_postfix (prior : List ParseDiagnostic) :
    expressionUnary literalExpression blockParser (state successSuffix 0 prior) = .ok wrapped (successState prior) ∧
    (successState prior).diagnostics = prior ++ [nameEvent] ∧
    (successState prior).peek? = some (sym 10 11 .semicolon) := by
  refine ⟨success_of_trace (input := state successSuffix 0 prior) success_trace, ?_, rfl⟩
  simp only [successState, State.diagnostics, List.reverse_cons, List.reverse_reverse]

theorem unary_ast_order_and_spans :
    wrapped = { span := span 0 10, value := .unary ⟨span 0 1, .logicalNot⟩ {
      span := span 1 10, value := .unary ⟨span 1 2, .bitNot⟩ {
        span := span 2 10, value := .field {
          span := span 2 8, value := .call nameValue args
        } (span 8 9) fieldName
      }
    }} := rfl

theorem duplicate_prior_diagnostics_survive_unary (prior : List ParseDiagnostic) :
    expressionUnary literalExpression blockParser (state successSuffix 0 (prior ++ [nameEvent, nameEvent])) =
      .ok wrapped (successState (prior ++ [nameEvent, nameEvent])) ∧
    (successState (prior ++ [nameEvent, nameEvent])).diagnostics = prior ++ [nameEvent, nameEvent, nameEvent] := by
  have result := source_order_prefix_wraps_maximal_postfix (prior ++ [nameEvent, nameEvent])
  exact ⟨result.1, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.2.1⟩

private def rejectSuffix : List Token := [sym 8 9 .dot, sym 9 10 .semicolon]
private def failure : Failure := {
  span := span 9 10, found := some (.symbol .semicolon)
  expected := { head := .identifier, tail := [] }, context := .expression
}
private def failedState (prior : List ParseDiagnostic) : State :=
  { state rejectSuffix 7 prior with diagnosticsRev := nameEvent :: prior.reverse }
private theorem rejection_trace : ExpressionUnaryTraceRejects postfixRejects source 99
    (rem rejectSuffix 0) (rem rejectSuffix 7) failure.toDiagnostic [nameEvent] := by
  apply ExpressionUnaryTraceRejects.postfixRejected (prefix_trace rejectSuffix)
  apply ExpressionPostfixTraceRejects.tailRejected (tailEvents := []) (atom_name rejectSuffix)
  apply PostfixTailTraceRejects.callLaterRejected (afterArguments := rem rejectSuffix 6)
    (argumentEvents := []) (tailEvents := [])
  · simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym]
  · exact arguments_trace rejectSuffix
  · apply PostfixTailTraceRejects.fieldNameRejected (afterDot := rem rejectSuffix 7) (span 8 9)
    · simp [TokenKindAbsentAt, TokenAt, rem, tokens, rejectSuffix, sym]
    · simp [TokenKindAbsentAt, TokenAt, rem, tokens, rejectSuffix, sym]
    · exact ⟨⟨by decide, rfl⟩, rfl⟩
    · simp [IdentifierAbsentAt, TokenAt, rem, tokens, rejectSuffix, sym]
    · exact .reported (.token (current := sym 9 10 .semicolon) ⟨by decide, rfl⟩)

/-- Prefix operators emit nothing, the checked name remains emitted, and the
terminal field report remains uncommitted even after a successful call suffix. -/
theorem postfix_failure_after_prefix_preserves_only_prior_events (prior : List ParseDiagnostic) :
    expressionUnary literalExpression blockParser (state rejectSuffix 0 prior) = .reject failure (failedState prior) ∧
    (failedState prior).diagnostics = prior ++ [nameEvent] ∧
    (failedState prior).peek? = some (sym 9 10 .semicolon) := by
  refine ⟨reject_of_trace (input := state rejectSuffix 0 prior) rejection_trace, ?_, rfl⟩
  simp only [failedState, State.diagnostics, List.reverse_cons, List.reverse_reverse]

private def minusInput (prior : List ParseDiagnostic) : State :=
  { state [] 0 prior with tokens := #[sym 0 1 .minus, sym 1 2 .bang], window := { endIndex := 2, endByte := 99 } }
private def hiddenInput (prior : List ParseDiagnostic) : State :=
  { state [] 0 prior with window := { endIndex := 0, endByte := 99 } }
private def missingInput (prior : List ParseDiagnostic) : State :=
  { state [] 0 prior with tokens := #[], window := { endIndex := 3, endByte := 99 } }

/-- Leading minus is not a canonical unary token, so it and the following bang
remain untouched. The independent absent guard drives the exact silent result. -/
theorem minus_stops_prefix_scanning (prior : List ParseDiagnostic) :
    unaryOperators 3 [] (minusInput prior) = .ok [] (minusInput prior) ∧
    (minusInput prior).peek? = some (sym 0 1 .minus) ∧
    (minusInput prior).tokens[1]? = some (sym 1 2 .bang) := by
  refine ⟨unaryOperators_trace_success_complete (input := minusInput prior) (.done ?_), rfl, rfl⟩
  simp [UnaryOperatorAbsentAt, TokenKindAbsentAt, TokenAt, minusInput, state, State.declarativeRemainder, sym]

theorem hidden_and_missing_prefixes_are_silent (prior : List ParseDiagnostic) :
    unaryOperators 1 [] (hiddenInput prior) = .ok [] (hiddenInput prior) ∧
    unaryOperators 4 [] (missingInput prior) = .ok [] (missingInput prior) ∧
    (hiddenInput prior).tokens[0]? = some (sym 0 1 .bang) ∧
    (hiddenInput prior).peek? = none ∧ (missingInput prior).atEnd = false := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · exact unaryOperators_trace_success_complete (input := hiddenInput prior) (.done (by
      simp [UnaryOperatorAbsentAt, TokenKindAbsentAt, TokenAt, hiddenInput, State.declarativeRemainder]))
  · exact unaryOperators_trace_success_complete (input := missingInput prior) (.done (by
      simp [UnaryOperatorAbsentAt, TokenKindAbsentAt, TokenAt, missingInput, State.declarativeRemainder]))

end Solcore.Test.SyntaxExpressionUnaryTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxExpressionValidity
/-! External consumers for recursive canonical expression validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @FunctionParameter.ValidFor
example := @LambdaParameter.ValidFor
example := @Block.ValidFor
example := @Expr.ValidFor
example := @Expr.ValidFor.span_valid

example (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (span : SourceSpan) (name : Identifier)
    (spanValid : span.ValidFor file) (nameValid : name.span.ValidFor file) :
    Expr.ValidFor statementValid file {
      span
      value := .identifier name
    } :=
  .identifier spanValid nameValid

example (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (span : SourceSpan)
    (callee : Expr) (arguments : DelimitedList Expr)
    (spanValid : span.ValidFor file)
    (calleeValid : Expr.ValidFor statementValid file callee)
    (argumentsSpanValid : arguments.span.ValidFor file)
    (argumentsValid : ∀ argument ∈ arguments.elements,
      Expr.ValidFor statementValid file argument) :
    Expr.ValidFor statementValid file {
      span
      value := .call callee arguments
    } :=
  .call spanValid calleeValid argumentsSpanValid argumentsValid

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionConditionalTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionConditionalTotalityProperties

open Solcore.Syntax.Parser.ExpressionInternals

example := @conditionalTail_ordinary_of_fuels
example := @conditionalTail_ne_invariant_of_fuels
example := @conditional_ordinary_of_elementFuels
example := @conditional_ne_invariant_of_elementFuels

end Solcore.Test.SyntaxParserExpressionConditionalTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionFuelContractProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionFuelContractProperties

open Solcore.Syntax.Parser.ExpressionInternals

example := @leftAssociative_fuelTotalityContract
example := @nonAssociative_fuelTotalityContract
example := @expressionUnary_fuelTotalityContract
example := @conditional_fuelTotalityContract

end Solcore.Test.SyntaxParserExpressionFuelContractProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionLambdaTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionLambdaTotalityProperties

open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @lambdaExpression_invariantFreeOnValid
example := @lambdaExpression_ne_invariant
example := @lambdaExpression_elementTotalityContract

end Solcore.Test.SyntaxParserExpressionLambdaTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionLayerConcreteFuelContractProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionLayerConcreteFuelContractProperties

open Solcore.Syntax.Parser.ExpressionInternals

example := @expressionLayer_concrete_fuelTotalityContract

end Solcore.Test.SyntaxParserExpressionLayerConcreteFuelContractProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionLayerFuelContractProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionLayerFuelContractProperties

open Solcore.Syntax.Parser.ExpressionInternals

example := @expressionLayer_fuelTotalityContract

end Solcore.Test.SyntaxParserExpressionLayerFuelContractProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionLeftAssociativeTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionLeftAssociativeTotalityProperties

open Solcore.Syntax.Parser.ExpressionInternals

example := @leftAssociativeTail_ordinary_of_fuels
example := @leftAssociativeTail_ne_invariant_of_fuels
example := @leftAssociative_ordinary_of_elementFuel
example := @leftAssociative_ne_invariant_of_elementFuel

end Solcore.Test.SyntaxParserExpressionLeftAssociativeTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionNameTraceProperties
/-! Real Boolean and checked-name expressions, including exact hyphen events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionNameTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @expressionNameTrace_outcome_total
example := @identifierExpressionTrace_exactOutcomeSpec
example := @identifierExpressionTrace_outcomeExists
example := @identifierExpression_trace_reject_sound
example := @identifierExpression_trace_reject_complete

theorem boolean_true_has_priority_and_is_silent {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .keyword .trueKw }) :
    expressionName input = .ok { span, value := "true" } { input with cursor := input.cursor + 1 } := by
  simpa only [List.reverse_nil, List.nil_append] using
    expressionName_eq_ok_of_trace (.boolean ⟨.trueKeyword token, rfl⟩)

theorem boolean_false_expression_is_identifier_shaped {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .keyword .falseKw }) :
    identifierExpression input = .ok {
      span, value := .identifier { span, value := "false" }
    } { input with cursor := input.cursor + 1 } := by
  simpa only [List.reverse_nil, List.nil_append] using
    identifierExpression_eq_ok_of_trace (.parsed (.boolean ⟨.falseKeyword token, rfl⟩))

private theorem boolean_absent_of_identifier {input : Remainder} {name : Identifier}
    (token : TokenAt input.tokens input.endIndex input.cursor
      { span := name.span, value := .identifier name.value }) : BooleanPatternAbsentAt input := by
  constructor
  · rintro ⟨span, current⟩; cases TokenAt.token_unique token current
  · rintro ⟨span, current⟩; cases TokenAt.token_unique token current

/-- Multiple hyphens still contribute exactly one checked-spelling event,
after all earlier events; the full output state and identifier AST are fixed. -/
theorem multiple_hyphens_emit_once {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .identifier "a-b-c" }) :
    identifierExpression input = .ok {
      span, value := .identifier { span, value := "a-b-c" }
    } { input with
      cursor := input.cursor + 1
      diagnosticsRev := { span, kind := .invalidIdentifierHyphen "a-b-c" } :: input.diagnosticsRev } := by
  have parsed : IdentifierParses input.declarativeRemainder { span, value := "a-b-c" }
      { input.declarativeRemainder with cursor := input.cursor + 1 } := ⟨token, rfl, rfl, rfl⟩
  have traced : IdentifierExpressionTraceParses input.file.id input.window.endByte
      input.declarativeRemainder { span, value := .identifier { span, value := "a-b-c" } }
      { input.declarativeRemainder with cursor := input.cursor + 1 }
      [{ span, kind := .invalidIdentifierHyphen "a-b-c" }] :=
    .parsed (.identifier (boolean_absent_of_identifier (name := { span, value := "a-b-c" }) token)
      (.parsed parsed (.hyphen (by change '-' ∈ "a-b-c".toList; decide))))
  exact identifierExpression_eq_ok_of_trace traced

theorem clean_name_keeps_every_prior_event {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .identifier "plain" }) :
    expressionName input = .ok { span, value := "plain" } { input with cursor := input.cursor + 1 } := by
  have parsed : IdentifierParses input.declarativeRemainder { span, value := "plain" }
      { input.declarativeRemainder with cursor := input.cursor + 1 } := ⟨token, rfl, rfl, rfl⟩
  simpa only [List.reverse_nil, List.nil_append] using expressionName_eq_ok_of_trace (input := input)
    (.identifier (boolean_absent_of_identifier (name := { span, value := "plain" }) token)
      (.parsed parsed (.clean (by change ¬ '-' ∈ "plain".toList; decide))))

/-- Failure after Boolean guards expects an identifier, not the Boolean
primitive's expression category, and retains the complete input state. -/
theorem non_name_reports_identifier_expectation {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .symbol .semicolon }) :
    identifierExpression input = .reject {
      span, found := some (.symbol .semicolon)
      expected := { head := .identifier, tail := [] }, context := .expression
    } input := by
  have noBoolean : BooleanPatternAbsentAt input.declarativeRemainder := by
    constructor
    · rintro ⟨otherSpan, current⟩; cases TokenAt.token_unique token current
    · rintro ⟨otherSpan, current⟩; cases TokenAt.token_unique token current
  have noName : IdentifierAbsentAt input.declarativeRemainder := by
    rintro ⟨otherSpan, text, current⟩; cases TokenAt.token_unique token current
  have current : CurrentInputAt input.file.id input.window.endByte input.declarativeRemainder
      span (some (.symbol .semicolon)) :=
    .token (current := { span, value := .symbol .semicolon }) token
  exact (identifierExpression_trace_reject_failure_iff.mp
    ⟨noBoolean, .absent noName, .reported current, rfl⟩).1

/-- The actual identifier-expression leaf closes the nonempty return trace
without a caller-supplied expression contract, including its single hyphen report. -/
theorem real_name_return_keeps_hyphen_event
    {input : State} {afterMarker afterValue after : Remainder} {name : Identifier}
    {markerSpan semicolonSpan : SourceSpan}
    (marker : ExactTokenParses (.keyword .returnKw) input.declarativeRemainder markerSpan afterMarker)
    (nameParsed : IdentifierParses afterMarker name afterValue)
    (hyphen : IdentifierHyphenSpelling name.value)
    (semicolon : ExactTokenParses (.symbol .semicolon) afterValue semicolonSpan after) :
    ∃ output, returnStatement identifierExpression input = .ok {
        span := SourceSpan.cover markerSpan semicolonSpan
        value := .returnStmt (some { span := name.span, value := .identifier name })
      } output ∧ output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ [{ span := name.span, kind := .invalidIdentifierHyphen name.value }] := by
  have notSemicolon : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex
      afterMarker.cursor (.symbol .semicolon) := by
    rintro ⟨span, current⟩; cases TokenAt.token_unique nameParsed.1 current
  exact returnStatement_trace_success_complete identifierExpression_trace_success_complete
    (.parsed markerSpan semicolonSpan marker
      (.present notSemicolon (.parsed (.identifier (boolean_absent_of_identifier nameParsed.1)
        (.parsed nameParsed (.hyphen hyphen))))) semicolon)

end Solcore.Test.SyntaxParserExpressionNameTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionNonAssociativeTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionNonAssociativeTotalityProperties

open Solcore.Syntax.Parser.ExpressionInternals

example := @nonAssociative_ordinary_of_elementFuel
example := @nonAssociative_ne_invariant_of_elementFuel

end Solcore.Test.SyntaxParserExpressionNonAssociativeTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionPostfixFuelContractProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionPostfixFuelContractProperties

open Solcore.Syntax.Parser.ExpressionInternals

example := @expressionPostfix_fuelTotalityContract

end Solcore.Test.SyntaxParserExpressionPostfixFuelContractProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionPostfixTailFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionPostfixTailFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @postfixTail_ordinary_of_fuel
example := @postfixTail_ne_invariant_of_fuel
example := @postfixTail_production_ordinary

end Solcore.Test.SyntaxParserExpressionPostfixTailFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionPostfixTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionPostfixTotalityProperties

open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @expressionPostfix_ordinary_of_elementFuel
example := @expressionPostfix_ne_invariant_of_elementFuel

end Solcore.Test.SyntaxParserExpressionPostfixTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionProperties
/-! External consumers for canonical Core expression-layer contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax.Parser

example := @ExpressionInternals.unaryOperators_validFor
example := @ExpressionInternals.unaryOperators_preservesTokenWindow
example := @ExpressionInternals.unaryOperators_preservesTokensOnSuccess
example := @ExpressionInternals.unaryOperators_cursorMonotoneOnSuccess
example := @ExpressionInternals.applyUnaryOperators_preservesBaseEnd
example := @ExpressionInternals.applyUnaryOperators_validFor
example := @ExpressionInternals.binaryAtPrecedence?_some_state_shape
example := @ExpressionInternals.binaryAtPrecedence?_validFor
example := @ExpressionInternals.consumeBinary_ok_state_shape
example := @ExpressionInternals.consumeBinary_reply_validFor
example := @ExpressionInternals.consumeBinary_preservesTokenWindow
example := @ExpressionInternals.consumeBinary_preservesTokensOnSuccess
example := @ExpressionInternals.consumeBinary_cursor_lt_onSuccess
example := @ExpressionInternals.consumeBinary_cursorMonotoneOnSuccess
example := @ExpressionInternals.binaryNode_validFor
example := @ExpressionInternals.binaryNode_startByte
example := @ExpressionInternals.binaryNode_endByte
example := @ExpressionInternals.leftAssociativeTail_preservesTokenWindow
example := @ExpressionInternals.leftAssociativeTail_preservesTokensOnSuccess
example := @ExpressionInternals.leftAssociativeTail_cursorMonotoneOnSuccess
example := @ExpressionInternals.leftAssociativeTail_preservesLeftStartOnSuccess
example := @ExpressionInternals.leftAssociativeTail_validFor
example := @ExpressionInternals.leftAssociative_preservesTokenWindow
example := @ExpressionInternals.leftAssociative_preservesTokensOnSuccess
example := @ExpressionInternals.leftAssociative_cursorMonotoneOnSuccess
example := @ExpressionInternals.leftAssociative_startsAtCurrentTokenOnSuccess
example := @ExpressionInternals.leftAssociative_validFor
example := @ExpressionInternals.nonAssociative_preservesTokenWindow
example := @ExpressionInternals.nonAssociative_preservesTokensOnSuccess
example := @ExpressionInternals.nonAssociative_cursorMonotoneOnSuccess
example := @ExpressionInternals.nonAssociative_startsAtCurrentTokenOnSuccess
example := @ExpressionInternals.nonAssociative_validFor
example := @ExpressionInternals.conditional_cursor_lt_onSuccess
example := @ExpressionInternals.expressionUnary_cursor_lt_onSuccess
example := @ExpressionInternals.leftAssociative_cursor_lt_onSuccess
example := @ExpressionInternals.nonAssociative_cursor_lt_onSuccess
example := @ExpressionInternals.ExpressionContract
example := @ExpressionInternals.ExpressionContract.preservesTokensOnSuccess
example := @ExpressionInternals.ExpressionContract.cursorMonotoneOnSuccess
example := @ExpressionInternals.ExpressionContract.atom
example := @ExpressionInternals.ExpressionContract.concretePostfix
example := @ExpressionInternals.ExpressionContract.unary
example := @ExpressionInternals.ExpressionContract.leftAssociative
example := @ExpressionInternals.ExpressionContract.nonAssociative
example := @ExpressionInternals.ExpressionContract.conditional
example := @ExpressionInternals.expressionLayer_contract
example := @ExpressionInternals.expressionLayer_concrete_contract
example := @ExpressionInternals.expressionLayer_validFor
example := @ExpressionInternals.expressionLayer_preservesTokenWindow
example := @ExpressionInternals.expressionLayer_preservesTokensOnSuccess
example := @ExpressionInternals.expressionLayer_cursor_lt_onSuccess
example := @ExpressionInternals.expressionLayer_cursorMonotoneOnSuccess
example := @ExpressionInternals.expressionLayer_startsAtCurrentTokenOnSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionUnaryLayerTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionUnaryLayerTotalityProperties

open Solcore.Syntax.Parser.ExpressionInternals

example := @expressionUnary_ordinary_of_postfixFuel
example := @expressionUnary_ne_invariant_of_postfixFuel

end Solcore.Test.SyntaxParserExpressionUnaryLayerTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionUnaryTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionUnaryTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionInternals

example := @unaryOperators_exists_ok_of_remainingCount_lt
example := @unaryOperators_ordinary_of_remainingCount_lt
example := @unaryOperators_ne_invariant_of_remainingCount_lt
example := @unaryOperators_production_exists_ok
example := @unaryOperators_production_ordinary
example := @unaryOperators_production_invariantFreeOnValid
example := @unaryOperators_production_ne_invariant

example (operatorsRev : List (Located UnaryOp)) :
    Parser.Ordinary (fun state =>
      unaryOperators (state.remainingCount + 1) operatorsRev state) :=
  unaryOperators_production_ordinary operatorsRev

end Solcore.Test.SyntaxParserExpressionUnaryTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPatternArgumentsFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternArgumentsFuelTotalityProperties

open Solcore.Syntax.Parser.PatternInternals

example := @requirePatternArguments_ok_of_delimitedNoTrailing_false_ok
example := @constructorArguments_ordinary_of_elementFuel
example := @constructorArguments_ne_invariant_of_elementFuel
example := @optionalConstructorArguments_ordinary_of_elementFuel
example := @optionalConstructorArguments_ne_invariant_of_elementFuel

end Solcore.Test.SyntaxParserPatternArgumentsFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPatternConstructorFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternConstructorFuelTotalityProperties

open Solcore.Syntax.Parser.PatternInternals

example := @dotConstructorPattern_ordinary_of_elementFuel
example := @dotConstructorPattern_ne_invariant_of_elementFuel

end Solcore.Test.SyntaxParserPatternConstructorFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPatternCoreFuelContractProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternCoreFuelContractProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PatternInternals

example := @patternCore_weakValidFor
example := @patternCore_fuelElementTotalityContract

end Solcore.Test.SyntaxParserPatternCoreFuelContractProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPatternCoreFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternCoreFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PatternInternals

example (nested : Parser Pattern) (expression : Parser Expr)
    (nestedFuel expressionFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (expressionContract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (expressionAdequate : input.remainingCount < expressionFuel + 1)
    (error : ParserInvariantError) :
    patternCore nested expression input ≠ .invariant error :=
  patternCore_ne_invariant_of_elementFuel nested expression nestedFuel
    expressionFuel nestedContract expressionContract input inputValid
    nestedAdequate expressionAdequate error

end Solcore.Test.SyntaxParserPatternCoreFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPatternCoreStrictProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternCoreStrictProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PatternInternals

example := @patternCore_cursor_lt_onSuccess

end Solcore.Test.SyntaxParserPatternCoreStrictProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPatternLayerFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternLayerFuelTotalityProperties

open Solcore.Syntax.Parser.PatternInternals

example := @patternLayer_ordinary_of_elementFuel
example := @patternLayer_ne_invariant_of_elementFuel
example := @patternLayer_cursor_lt_onSuccess
example := @patternLayer_fuelElementTotalityContract

end Solcore.Test.SyntaxParserPatternLayerFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPatternLeafFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternLeafFuelTotalityProperties

open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PatternInternals

example := @comptimePattern_ordinary_of_elementFuel
example := @comptimePattern_ne_invariant_of_elementFuel

end Solcore.Test.SyntaxParserPatternLeafFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPatternLeafTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternLeafTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PatternInternals

example : Parser.Ordinary wildcardPattern := wildcardPattern_ordinary
example : ElementTotalityContract patternName :=
  patternName_elementTotalityContract

example (expression : Parser Expr)
    (contract : ElementTotalityContract expression) :
    Parser.InvariantFreeOnValid (comptimePattern expression) :=
  comptimePattern_invariantFreeOnValid expression contract

end Solcore.Test.SyntaxParserPatternLeafTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPatternProperties
/-! External consumers for canonical pattern parser contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example (expressionValid : SourceFile → Expr → Prop) :
    PatternInternals.wildcardPattern.ValidFor
      (Pattern.ValidFor expressionValid) :=
  PatternInternals.wildcardPattern_validFor expressionValid

example : Parser.PreservesTokenWindow
    PatternInternals.wildcardPattern :=
  PatternInternals.wildcardPattern_preservesTokenWindow

example : Parser.PreservesTokensOnSuccess
    PatternInternals.wildcardPattern :=
  PatternInternals.wildcardPattern_preservesTokensOnSuccess

example : Parser.CursorMonotoneOnSuccess
    PatternInternals.wildcardPattern :=
  PatternInternals.wildcardPattern_cursorMonotoneOnSuccess

example : Parser.StartsAtCurrentTokenOnSuccess
    PatternInternals.wildcardPattern (·.span) :=
  PatternInternals.wildcardPattern_startsAtCurrentTokenOnSuccess

example := PatternInternals.literalPattern_validFor
example := PatternInternals.literalPattern_preservesTokenWindow
example := PatternInternals.literalPattern_preservesTokensOnSuccess
example := PatternInternals.literalPattern_cursorMonotoneOnSuccess
example := PatternInternals.literalPattern_startsAtCurrentTokenOnSuccess
example := PatternInternals.booleanBinderPattern_validFor
example := PatternInternals.booleanBinderPattern_preservesTokenWindow
example := PatternInternals.booleanBinderPattern_preservesTokensOnSuccess
example := PatternInternals.booleanBinderPattern_cursorMonotoneOnSuccess
example := PatternInternals.booleanBinderPattern_startsAtCurrentTokenOnSuccess
example := PatternInternals.patternName_validFor
example := PatternInternals.patternName_preservesTokenWindow
example := PatternInternals.patternName_preservesTokensOnSuccess
example := PatternInternals.patternName_cursorMonotoneOnSuccess
example := PatternInternals.patternName_startsAtCurrentTokenOnSuccess
example := PatternInternals.requirePatternArguments_validFor
example := PatternInternals.constructorArguments_validFor
example := PatternInternals.constructorArguments_preservesTokenWindow
example := PatternInternals.constructorArguments_preservesTokensOnSuccess
example := PatternInternals.constructorArguments_cursorMonotoneOnSuccess
example := PatternInternals.constructorArguments_startsAtCurrentTokenOnSuccess
example := PatternInternals.optionalConstructorArguments_validFor
example := PatternInternals.optionalConstructorArguments_preservesTokenWindow
example :=
  PatternInternals.optionalConstructorArguments_preservesTokensOnSuccess
example := PatternInternals.optionalConstructorArguments_cursorMonotoneOnSuccess
example := PatternInternals.closePatternTuple_validFor
example := PatternInternals.closePatternTuple_preservesTokenWindow
example := PatternInternals.closePatternTuple_preservesTokensOnSuccess
example := PatternInternals.closePatternTuple_cursorMonotoneOnSuccess
example := PatternInternals.closePatternTuple_preservesOpeningStartOnSuccess
example := PatternInternals.closePatternTuple_endsAtCurrentTokenOnSuccess
example := PatternInternals.patternTupleTail_validFor
example := PatternInternals.patternTupleTail_preservesTokenWindow
example := PatternInternals.patternTupleTail_preservesTokensOnSuccess
example := PatternInternals.patternTupleTail_cursorMonotoneOnSuccess
example := PatternInternals.patternTupleTail_preservesOpeningStartOnSuccess
example := PatternInternals.parenthesizedPattern_validFor
example := PatternInternals.parenthesizedPattern_preservesTokenWindow
example := PatternInternals.parenthesizedPattern_preservesTokensOnSuccess
example := PatternInternals.parenthesizedPattern_cursorMonotoneOnSuccess
example := PatternInternals.parenthesizedPattern_startsAtCurrentTokenOnSuccess
example := PatternInternals.dotConstructorPattern_validFor
example := PatternInternals.dotConstructorPattern_preservesTokenWindow
example := PatternInternals.dotConstructorPattern_preservesTokensOnSuccess
example := PatternInternals.dotConstructorPattern_cursorMonotoneOnSuccess
example := PatternInternals.dotConstructorPattern_startsAtCurrentTokenOnSuccess
example := PatternInternals.qualifiedPattern_validFor
example := PatternInternals.qualifiedPattern_preservesTokenWindow
example := PatternInternals.qualifiedPattern_preservesTokensOnSuccess
example := PatternInternals.qualifiedPattern_cursorMonotoneOnSuccess
example := PatternInternals.qualifiedPattern_startsAtCurrentTokenOnSuccess
example := PatternInternals.comptimePattern_validFor
example := PatternInternals.comptimePattern_preservesTokenWindow
example := PatternInternals.comptimePattern_preservesTokensOnSuccess
example := PatternInternals.comptimePattern_cursorMonotoneOnSuccess
example := PatternInternals.comptimePattern_startsAtCurrentTokenOnSuccess
example := PatternInternals.patternCore_validFor
example := PatternInternals.patternCore_preservesTokenWindow
example := PatternInternals.patternCore_preservesTokensOnSuccess
example := PatternInternals.patternCore_cursorMonotoneOnSuccess
example := PatternInternals.patternCore_startsAtCurrentTokenOnSuccess
example := PatternInternals.finishRecoveredPattern_validFor
example := PatternInternals.recoverPatternAux_validFor
example := PatternInternals.finishRecoveredPattern_preservesTokenWindow
example := PatternInternals.recoverPatternAux_preservesTokenWindow
example := PatternInternals.recoverPatternAux_preservesTokensOnSuccess
example := PatternInternals.recoverPatternAux_cursorMonotoneOnSuccess
example := PatternInternals.recoverPatternAux_startsAtFirstSpanOnSuccess
example {input afterToken next : State} {token : Token} {pattern : Pattern}
    (last : SourceSpan) (fuel : Nat)
    (advanced : input.advance? = some (token, afterToken))
    (parsed : PatternInternals.recoverPatternAux token.span last fuel
      afterToken = .ok pattern next) :
    ∃ firstToken, input.peek? = some firstToken ∧
      firstToken.span.startByte = pattern.span.startByte :=
  PatternInternals.recoverPatternAux_startsAtAdvancedCurrentTokenOnSuccess
    last fuel advanced parsed
example := PatternInternals.patternLayer_validFor
example := PatternInternals.patternLayer_preservesTokenWindow
example := PatternInternals.patternLayer_preservesTokensOnSuccess
example := PatternInternals.patternLayer_cursorMonotoneOnSuccess
example := PatternInternals.patternLayer_startsAtCurrentTokenOnSuccess
example := TermInternals.corePatternWithFuel_validFor
example := TermInternals.corePatternWithFuel_preservesTokenWindow
example := TermInternals.corePatternWithFuel_preservesTokensOnSuccess
example := TermInternals.corePatternWithFuel_cursorMonotoneOnSuccess
example := TermInternals.corePatternWithFuel_startsAtCurrentTokenOnSuccess
example := pattern_validFor_of_coreExpression
example := pattern_preservesTokenWindow_of_coreExpression
example := pattern_preservesTokensOnSuccess_of_coreExpression
example := pattern_cursorMonotoneOnSuccess_of_coreExpression
example := pattern_startsAtCurrentTokenOnSuccess_of_coreExpression

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPatternQualifiedFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternQualifiedFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PatternInternals

example (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    qualifiedPattern nested input ≠ .invariant error :=
  qualifiedPattern_ne_invariant_of_elementFuel nested nestedFuel contract
    input inputValid adequate error

end Solcore.Test.SyntaxParserPatternQualifiedFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPatternRecoveryTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternRecoveryTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PatternInternals

example := @recoverPatternAux_exists_ok_of_remainingCount_lt
example := @recoverPatternAux_ordinary_of_remainingCount_lt
example := @recoverPatternAux_ne_invariant_of_remainingCount_lt
example := @recoverPatternAux_production_exists_ok
example := @recoverPatternAux_production_ordinary
example := @recoverPatternAux_production_invariantFreeOnValid
example := @recoverPatternAux_production_ne_invariant

end Solcore.Test.SyntaxParserPatternRecoveryTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPatternTupleTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPatternTupleTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PatternInternals

example := @closePatternTuple_invariantFreeOnValid
example := @patternTupleTail_ordinary_of_elementFuel
example := @patternTupleTail_ne_invariant_of_elementFuel
example := @patternTupleTail_production_ordinary_of_elementFuel
example := @patternTupleTail_production_ne_invariant_of_elementFuel
example := @parenthesizedPattern_ordinary_of_elementFuel
example := @parenthesizedPattern_ne_invariant_of_elementFuel

example (nested : Parser Pattern) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, parenthesizedPattern nested input = .ok value next) ∨
      (∃ failure next,
        parenthesizedPattern nested input = .reject failure next) :=
  parenthesizedPattern_ordinary_of_elementFuel nested nestedFuel contract input
    inputValid adequate

end Solcore.Test.SyntaxParserPatternTupleTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxPatternValidity
/-! External consumers for recursive canonical pattern validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @Pattern.ValidFor
example := @Pattern.ValidFor.span_valid

example (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) (span marker : SourceSpan)
    (spanValid : span.ValidFor file) (markerValid : marker.ValidFor file) :
    Pattern.ValidFor expressionValid file {
      span
      value := .wildcard marker
    } :=
  .wildcard spanValid markerValid

example (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) (span : SourceSpan)
    (elements : DelimitedList Pattern)
    (spanValid : span.ValidFor file)
    (elementsSpanValid : elements.span.ValidFor file)
    (elementsValid : ∀ element ∈ elements.elements,
      Pattern.ValidFor expressionValid file element) :
    Pattern.ValidFor expressionValid file {
      span
      value := .tuple elements
    } :=
  .tuple spanValid elementsSpanValid elementsValid

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxPostfixTailProgressSupport
/-! Exact test children are defined by independent remainder transformations.
They preserve diagnostic prefixes and have no rejection outcomes; their window
contract requires only that the transformation preserve the numeric endIndex. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxPostfixTailProgressSupport

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

def source : SourceId := { origin := .main, path := "postfix-progress.sol" }
def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
def sym (startByte endByte : Nat) (kind : Symbol) : Token := { span := span startByte endByte, value := .symbol kind }
def name (startByte endByte : Nat) : Token := { span := span startByte endByte, value := .identifier "x" }
def fixed : Expr := { span := span 0 1, value := .error }
def remainder (tokens : Array Token) (cursor endIndex : Nat) : Remainder := { tokens, cursor, endIndex }
def state (before : Remainder) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := before.tokens, cursor := before.cursor
  window := { endIndex := before.endIndex, endByte := 6 }, diagnosticsRev := prior.reverse
}

def child (step : Remainder → Remainder) : Parser Expr := fun input =>
  .ok fixed (input.traceResult (step input.declarativeRemainder) [])
def childTrace (step : Remainder → Remainder) (_source : SourceId) (_endByte : Nat)
    (input : Remainder) (value : Expr) (after : Remainder) (trace : List ParseDiagnostic) : Prop :=
  value = fixed ∧ after = step input ∧ trace = []
def neverReject (_source : SourceId) (_endByte : Nat) (_input _after : Remainder)
    (_report : ParseDiagnostic) (_trace : List ParseDiagnostic) : Prop := False

theorem child_success_sound (step : Remainder → Remainder) : ParserTraceSuccessSound (child step) (childTrace step) := by
  intro input output value result
  cases result
  exact ⟨[], ⟨rfl, input.traceResult_declarativeRemainder _ [], rfl⟩, input.traceResult_diagnostics _ []⟩

theorem child_success_complete (step : Remainder → Remainder) : ParserTraceSuccessComplete (child step) (childTrace step) := by
  rintro input value after trace ⟨rfl, rfl, rfl⟩
  exact ⟨_, rfl, input.traceResult_declarativeRemainder _ [], input.traceResult_diagnostics _ []⟩

theorem child_success_context (step : Remainder → Remainder)
    (endIndex : ∀ before, (step before).endIndex = before.endIndex) : ParserSuccessContext (child step) := by
  intro input output value result
  cases result
  exact ⟨rfl, by simp only [State.traceResult, endIndex, State.declarativeRemainder]⟩

theorem child_reject_sound (step : Remainder → Remainder) : ParserTraceRejectSound (child step) neverReject := by
  intro input output failure result
  cases result

theorem child_reject_complete (step : Remainder → Remainder) : ParserTraceRejectComplete (child step) neverReject := by
  intro input after report trace impossible
  exact False.elim impossible

theorem child_ordinary (step : Remainder → Remainder) : Parser.Ordinary (child step) :=
  fun _ => .inl ⟨_, _, rfl⟩

theorem child_exact (step : Remainder → Remainder) (sourceId : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec (childTrace step) neverReject sourceId endByte where
  successResultUnique := by
    rintro input left right afterLeft afterRight leftTrace rightTrace
      ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  rejectResultUnique := by intros; contradiction
  successRejectDisjoint := by intros; contradiction

theorem absent_of_token {input : Remainder} {token : Token} {kind : TokenKind}
    (found : TokenAt input.tokens input.endIndex input.cursor token) (different : token.value ≠ kind) :
    TokenKindAbsentAt input.tokens input.endIndex input.cursor kind := by
  rintro ⟨span, other⟩
  have same := Option.some.inj (found.2.symm.trans other.2)
  exact different (congrArg (fun item : Token => item.value) same)

end Solcore.Test.SyntaxPostfixTailProgressSupport
end

section
-- leanmerge: from Solcore.Test.SyntaxPostfixTailProgressProperties
/-! Index children need not advance: the closing bracket can finish the
suffix. Call lists instead reject stationary success as noProgress. A child
that preserves file/window but rewinds and replaces tokens gives a finite
independent index trace exceeding the production remaining-count fuel. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxPostfixTailProgressProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals SyntaxPostfixTailProgressSupport

private def indexBefore : Remainder := remainder #[sym 0 1 .leftBracket, sym 1 2 .rightBracket] 0 2
private def indexValue : Expr := postfixIndexTraceValue fixed fixed (span 0 1) (span 1 2)

private theorem index_opening : ExactTokenParses (.symbol .leftBracket) indexBefore
    (span 0 1) { indexBefore with cursor := 1 } :=
  ⟨⟨by decide, rfl⟩, rfl⟩
private theorem index_closing : ExactTokenParses (.symbol .rightBracket) { indexBefore with cursor := 1 }
    (span 1 2) { indexBefore with cursor := 2 } :=
  ⟨⟨by decide, rfl⟩, rfl⟩

theorem stationary_index_has_independent_trace :
    PostfixTailTraceParses (childTrace id) source 6 indexBefore fixed indexValue
      { indexBefore with cursor := 2 } [] := by
  apply PostfixTailTraceParses.index (indexEvents := []) (tailEvents := [])
    (span 0 1) (span 1 2) index_opening ⟨rfl, rfl, rfl⟩ index_closing
  exact .done (by simp [PostfixSuffixAbsentAt, TokenKindAbsentAt, TokenAt, indexBefore, remainder])

theorem stationary_index_child_does_not_advance (prior : List ParseDiagnostic) :
    child id { state indexBefore prior with cursor := 1 } =
      .ok fixed { state indexBefore prior with cursor := 1 } := rfl

/-- Whole Reply equality also retains arbitrary incoming diagnostic multiplicity. -/
theorem stationary_index_executes (block : Parser Block) (prior : List ParseDiagnostic) :
    postfixTail (child id) block 2 fixed (state indexBefore prior) =
      .ok indexValue { state indexBefore prior with cursor := 2 } := rfl

/-- The grammar-to-execution theorem consumes the independent token derivation. -/
theorem stationary_index_trace_executes_eventually (block : Parser Block) (prior : List ParseDiagnostic) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∃ output,
      postfixTail (child id) block fuel fixed (state indexBefore prior) = .ok indexValue output ∧
      output.declarativeRemainder = { indexBefore with cursor := 2 } ∧
      output.diagnostics = (state indexBefore prior).diagnostics ++ [] :=
  postfixTail_trace_success_complete_eventually (child_success_complete id)
    (child_success_context id (fun _ => rfl)) block stationary_index_has_independent_trace

private def callBefore : Remainder :=
  remainder #[sym 0 1 .leftParen, sym 1 2 .plus, sym 2 3 .rightParen] 0 3

theorem stationary_call_reaches_noProgress (block : Parser Block) (prior : List ParseDiagnostic) (fuel : Nat) :
    postfixTail (child id) block (fuel + 1) fixed (state callBefore prior) =
      .invariant (.noProgress .expression (span 1 2)) := rfl

/-- Finite-trace completeness excludes a fictitious ordinary call success;
the exact same child does have the independent index trace above. -/
theorem stationary_call_has_no_independent_success (block : Parser Block) (prior : List ParseDiagnostic) :
    ¬ ∃ value after trace, PostfixTailTraceParses (childTrace id) source 6
      callBefore fixed value after trace := by
  rintro ⟨value, after, trace, parsed⟩
  rcases postfixTail_trace_success_complete_eventually (child_success_complete id)
      (child_success_context id (fun _ => rfl)) block (input := state callBefore prior) parsed with ⟨bound, executes⟩
  rcases executes (bound + 1) (Nat.le_succ _) with ⟨output, result, _⟩
  rw [stationary_call_reaches_noProgress] at result
  contradiction

private def initialTokens : Array Token := #[name 0 1, sym 1 2 .leftBracket]
private def firstTokens : Array Token := #[sym 2 3 .rightBracket, sym 3 4 .leftBracket]
private def finalTokens : Array Token := #[sym 4 5 .rightBracket, name 5 6]
private def rewind (input : Remainder) : Remainder := {
  input with tokens := if input.tokens = initialTokens then firstTokens else finalTokens, cursor := 0
}
private def rewindBefore : Remainder := remainder initialTokens 1 2
private def afterFirst : Remainder := remainder firstTokens 0 2
private def afterSecond : Remainder := remainder finalTokens 0 2
private def firstValue : Expr := postfixIndexTraceValue fixed fixed (span 1 2) (span 2 3)
private def finalValue : Expr := postfixIndexTraceValue firstValue fixed (span 3 4) (span 4 5)

private theorem first_opening : ExactTokenParses (.symbol .leftBracket) rewindBefore (span 1 2)
    { rewindBefore with cursor := 2 } := ⟨⟨by decide, rfl⟩, rfl⟩
private theorem first_child : childTrace rewind source 6 { rewindBefore with cursor := 2 }
    fixed afterFirst [] := ⟨rfl, rfl, rfl⟩
private theorem first_closing : ExactTokenParses (.symbol .rightBracket) afterFirst (span 2 3)
    { afterFirst with cursor := 1 } := ⟨⟨by decide, rfl⟩, rfl⟩
private theorem second_opening : ExactTokenParses (.symbol .leftBracket) { afterFirst with cursor := 1 }
    (span 3 4) { afterFirst with cursor := 2 } := ⟨⟨by decide, rfl⟩, rfl⟩
private theorem second_child : childTrace rewind source 6 { afterFirst with cursor := 2 }
    fixed afterSecond [] := ⟨rfl, rfl, rfl⟩
private theorem second_closing : ExactTokenParses (.symbol .rightBracket) afterSecond (span 4 5)
    { afterSecond with cursor := 1 } := ⟨⟨by decide, rfl⟩, rfl⟩
private theorem final_stops : PostfixSuffixAbsentAt { afterSecond with cursor := 1 } := by
  have found : TokenAt finalTokens 2 1 (name 5 6) := ⟨by decide, rfl⟩
  exact ⟨absent_of_token found (by decide), absent_of_token found (by decide), absent_of_token found (by decide)⟩

/-- The independently defined child has all five trace contracts and ordinary
execution over every State; full-window context does not prohibit rewinding. -/
theorem rewinding_child_has_five_contracts_and_is_ordinary :
    ParserTraceSuccessSound (child rewind) (childTrace rewind) ∧
    ParserTraceSuccessComplete (child rewind) (childTrace rewind) ∧
    ParserSuccessContext (child rewind) ∧
    ParserTraceRejectSound (child rewind) neverReject ∧
    ParserTraceRejectComplete (child rewind) neverReject ∧
    Parser.Ordinary (child rewind) :=
  ⟨child_success_sound rewind, child_success_complete rewind, child_success_context rewind (fun _ => rfl),
    child_reject_sound rewind, child_reject_complete rewind, child_ordinary rewind⟩

theorem rewinding_has_finite_independent_trace :
    PostfixTailTraceParses (childTrace rewind) source 6 rewindBefore fixed finalValue
      { afterSecond with cursor := 1 } [] :=
  .index (span 1 2) (span 2 3) first_opening first_child first_closing
    (.index (span 3 4) (span 4 5) second_opening second_child second_closing (.done final_stops))

theorem rewinding_trace_executes_eventually (block : Parser Block) (prior : List ParseDiagnostic) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∃ output,
      postfixTail (child rewind) block fuel fixed (state rewindBefore prior) = .ok finalValue output ∧
      output.declarativeRemainder = { afterSecond with cursor := 1 } ∧
      output.diagnostics = (state rewindBefore prior).diagnostics ++ [] :=
  postfixTail_trace_success_complete_eventually (child_success_complete rewind)
    (child_success_context rewind (fun _ => rfl)) block rewinding_has_finite_independent_trace

/-- The initial remaining count is one. Two suffixes consume all two units,
leaving no fuel to observe the final non-suffix token. -/
theorem rewinding_production_fuel_is_insufficient (block : Parser Block) (prior : List ParseDiagnostic) :
    postfixTail (child rewind) block ((state rewindBefore prior).remainingCount + 1)
      fixed (state rewindBefore prior) = .invariant (.fuelExhausted .expression (span 5 6)) := rfl

theorem rewinding_fuel_three_executes (block : Parser Block) (prior : List ParseDiagnostic) :
    postfixTail (child rewind) block 3 fixed (state rewindBefore prior) =
      .ok finalValue (state { afterSecond with cursor := 1 } prior) := rfl

theorem rewinding_has_no_strict_progress_contract (nestedFuel : Nat) :
    ¬ UnrestrictedFuelElementContract (child rewind) nestedFuel := by
  intro contract
  have result : child rewind { state rewindBefore [] with cursor := 2 } =
      .ok fixed (state afterFirst []) := rfl
  have progress := contract.cursorLtOnSuccess result
  change 2 < 0 at progress
  omega

end Solcore.Test.SyntaxPostfixTailProgressProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxPostfixTailTraceSupport
/-! Independent witnesses for a mixed `.a-b[1](2)` postfix prefix, shared
between successful maximal tails and later exact rejection consumers. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxPostfixTailTraceSupport

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals SyntaxExpressionAtomTotalityProperties

def source : SourceId := { origin := .main, path := "postfix-trace.sol" }
def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
def sym (first last : Nat) (kind : Symbol) : Token := { span := span first last, value := .symbol kind }
def name : Identifier := { span := span 2 5, value := "a-b" }
def nameEvent : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
def literal (first last : Nat) (spelling : String) : Expr := {
  span := span first last, value := .literal { span := span first last, value := .decimal spelling }
}
def base : Expr := { span := span 0 1, value := .identifier { span := span 0 1, value := "x" } }
def fieldValue : Expr := postfixFieldTraceValue base (span 1 2) name
def indexValue : Expr := postfixIndexTraceValue fieldValue (literal 6 7 "1") (span 5 6) (span 7 8)
def arguments : DelimitedList Expr := { span := span 8 11, elements := [literal 9 10 "2"] }
def callValue : Expr := postfixCallTraceValue indexValue arguments
def tokens (suffix : List Token) : List Token :=
  [sym 1 2 .dot, { span := name.span, value := .identifier name.value },
    sym 5 6 .leftBracket, { span := span 6 7, value := .decimalLiteral "1" }, sym 7 8 .rightBracket,
    sym 8 9 .leftParen, { span := span 9 10, value := .decimalLiteral "2" }, sym 10 11 .rightParen] ++ suffix
def rem (suffix : List Token) (cursor : Nat) : Remainder :=
  { tokens := (tokens suffix).toArray, endIndex := (tokens suffix).length, cursor }
def state (suffix : List Token) (cursor : Nat) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := (tokens suffix).toArray, cursor
  window := { endIndex := (tokens suffix).length, endByte := 99 }, diagnosticsRev := prior.reverse
}

theorem prefix_name (suffix : List Token) :
    IdentifierTraceParses (rem suffix 1) name (rem suffix 2) [nameEvent] :=
  .parsed ⟨⟨by simp [rem, tokens], rfl⟩, rfl, rfl, rfl⟩
    (.hyphen (by unfold IdentifierHyphenSpelling name; decide))

theorem prefix_index (suffix : List Token) :
    LiteralExpressionTraceParses source 99 (rem suffix 3) (literal 6 7 "1") (rem suffix 4) [] :=
  ⟨.parsed (.decimal ⟨by simp [rem, tokens], rfl⟩), rfl⟩

theorem prefix_arguments (suffix : List Token) :
    NoTrailingDelimitedListTraceParses .leftParen .rightParen true LiteralExpressionTraceParses
      source 99 (rem suffix 5) arguments (rem suffix 8) [] := by
  apply NoTrailingDelimitedListTraceParses.nonempty (afterOpening := rem suffix 6)
    (afterFirst := rem suffix 7) (first := literal 9 10 "2") (rest := [])
    (firstEvents := []) (tailEvents := []) (span 8 9) (span 10 11)
  · exact ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
  · exact .absent (by simp [TokenKindAbsentAt, TokenAt, rem, tokens])
  · exact ⟨.parsed (.decimal ⟨by simp [rem, tokens], rfl⟩), rfl⟩
  · change 6 < 7; decide
  · exact .close (by simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym])
      ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩

theorem prefix_success (suffix : List Token) {value : Expr} {after : Remainder} {trace : List ParseDiagnostic}
    (tail : PostfixTailTraceParses LiteralExpressionTraceParses source 99 (rem suffix 8) callValue value after trace) :
    PostfixTailTraceParses LiteralExpressionTraceParses source 99 (rem suffix 0) base value after ([nameEvent] ++ trace) := by
  apply PostfixTailTraceParses.field (afterDot := rem suffix 1) (afterName := rem suffix 2)
    (nameEvents := [nameEvent]) (tailEvents := trace) (span 1 2)
  · simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym]
  · simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym]
  · exact ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
  · exact prefix_name suffix
  · apply PostfixTailTraceParses.index (afterOpening := rem suffix 3) (afterIndex := rem suffix 4)
      (afterClosing := rem suffix 5) (indexEvents := []) (tailEvents := trace) (span 5 6) (span 7 8)
    · exact ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
    · exact prefix_index suffix
    · exact ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
    · exact .call (by simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym]) (prefix_arguments suffix) tail

theorem prefix_rejected (suffix : List Token) {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (tail : PostfixTailTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects source 99
      (rem suffix 8) callValue after report trace) :
    PostfixTailTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects source 99
      (rem suffix 0) base after report ([nameEvent] ++ trace) := by
  apply PostfixTailTraceRejects.fieldLaterRejected (afterDot := rem suffix 1) (afterName := rem suffix 2)
    (nameEvents := [nameEvent]) (tailEvents := trace) (span 1 2)
  · simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym]
  · simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym]
  · exact ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
  · exact prefix_name suffix
  · apply PostfixTailTraceRejects.indexLaterRejected (afterOpening := rem suffix 3) (afterIndex := rem suffix 4)
      (afterClosing := rem suffix 5) (indexEvents := []) (tailEvents := trace) (span 5 6) (span 7 8)
    · exact ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
    · exact prefix_index suffix
    · exact ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
    · exact .callLaterRejected (by simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym]) (prefix_arguments suffix) tail

theorem success_of_trace (block : Parser Block) {input : State} {initial value : Expr}
    {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : PostfixTailTraceParses LiteralExpressionTraceParses input.file.id input.window.endByte
      input.declarativeRemainder initial value after trace) :
    postfixTail literalExpression block (input.remainingCount + 1) initial input =
      .ok value (input.traceResult after trace) :=
  (postfixTail_trace_success_state_iff_of_ne_invariant literalExpression_trace_success_sound
    literalExpression_trace_reject_sound literalExpression_success_context block _ initial
    (literalExpressionTraceExactOutcomeSpec _ _).toTraceExactOutcomeSpec
    (postfixTail_production_ne_invariant_of_unrestrictedElementFuel literalExpression block
      input.remainingCount (literal_child_contract _) initial input (Nat.lt_succ_self _))).mp parsed

theorem reject_of_trace (block : Parser Block) {input : State} {initial : Expr}
    {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic}
    (rejection : PostfixTailTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects
      input.file.id input.window.endByte input.declarativeRemainder initial after failure.toDiagnostic trace) :
    postfixTail literalExpression block (input.remainingCount + 1) initial input =
      .reject failure (input.traceResult after trace) :=
  (postfixTail_trace_reject_failure_state_iff_of_ne_invariant literalExpression_trace_success_sound
    literalExpression_trace_reject_sound literalExpression_success_context
    (fun result => ⟨(literalExpression_reject_context result).1,
      congrArg TokenWindow.endByte (literalExpression_reject_context result).2⟩) block _ initial
    (literalExpressionTraceExactOutcomeSpec _ _).toTraceExactOutcomeSpec
    (postfixTail_production_ne_invariant_of_unrestrictedElementFuel literalExpression block
      input.remainingCount (literal_child_contract _) initial input (Nat.lt_succ_self _))).mp rejection

end Solcore.Test.SyntaxPostfixTailTraceSupport
end

section
-- leanmerge: from Solcore.Test.SyntaxPostfixTailTraceProperties
/-! Reverse consumers derive actual complete postfix replies from independent
token/trace witnesses. The literal child supplies the production fuel bound;
the arbitrary block is unused. These are maximal tails, not full expressions. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxPostfixTailTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals SyntaxPostfixTailTraceSupport

private def successfulSuffix : List Token := [sym 11 12 .semicolon]
private def finished (prior : List ParseDiagnostic) : State :=
  { state successfulSuffix 8 prior with diagnosticsRev := nameEvent :: prior.reverse }

private theorem successful_trace :
    PostfixTailTraceParses LiteralExpressionTraceParses source 99 (rem successfulSuffix 0)
      base callValue (rem successfulSuffix 8) [nameEvent] :=
  prefix_success successfulSuffix (.done (by
    simp [PostfixSuffixAbsentAt, TokenKindAbsentAt, TokenAt, successfulSuffix, rem, tokens, sym]))

/-- One warning precedes the silent index and call. The semicolon is unread,
and every complete State field, including arbitrary prior diagnostics, is fixed. -/
theorem mixed_suffixes_return_exact_state (block : Parser Block) (prior : List ParseDiagnostic) :
    postfixTail literalExpression block 10 base (state successfulSuffix 0 prior) =
      .ok callValue (finished prior) ∧
    (finished prior).diagnostics = prior ++ [nameEvent] ∧
    (finished prior).cursor = 8 ∧ (finished prior).peek? = some (sym 11 12 .semicolon) := by
  refine ⟨success_of_trace block (input := state successfulSuffix 0 prior) successful_trace, ?_, rfl, rfl⟩
  simp only [finished, State.diagnostics, List.reverse_cons, List.reverse_reverse]

/-- The nested AST retains separate base, field-dot, bracket, and call spans. -/
theorem mixed_suffix_ast_is_fully_located :
    callValue = {
      span := span 0 11
      value := .call {
        span := span 0 8
        value := .index {
          span := span 0 5
          value := .field base (span 1 2) name
        } (span 5 8) (literal 6 7 "1")
      } { span := span 8 11, elements := [literal 9 10 "2"] }
    } := rfl

theorem duplicate_prior_names_are_not_deduplicated (block : Parser Block) (prior : List ParseDiagnostic) :
    postfixTail literalExpression block 10 base (state successfulSuffix 0 (prior ++ [nameEvent, nameEvent])) =
      .ok callValue (finished (prior ++ [nameEvent, nameEvent])) ∧
    (finished (prior ++ [nameEvent, nameEvent])).diagnostics = prior ++ [nameEvent, nameEvent, nameEvent] := by
  have result := mixed_suffixes_return_exact_state block (prior ++ [nameEvent, nameEvent])
  exact ⟨result.1, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.2.1⟩

private def terminal (boolean : Bool) : Token :=
  if boolean then { span := span 12 16, value := .keyword .trueKw } else sym 12 13 .semicolon
private def rejectedSuffix (boolean : Bool) : List Token := [sym 11 12 .dot, terminal boolean]
private def terminalFailure (boolean : Bool) : Failure := {
  span := (terminal boolean).span, found := some (terminal boolean).value
  expected := { head := .identifier, tail := [] }, context := .expression
}
private def rejectedState (boolean : Bool) (prior : List ParseDiagnostic) : State :=
  { state (rejectedSuffix boolean) 9 prior with diagnosticsRev := nameEvent :: prior.reverse }

private theorem later_field_rejection (boolean : Bool) :
    PostfixTailTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects source 99
      (rem (rejectedSuffix boolean) 0) base (rem (rejectedSuffix boolean) 9)
      (terminalFailure boolean).toDiagnostic [nameEvent] := by
  apply prefix_rejected (trace := []) (rejectedSuffix boolean)
  apply PostfixTailTraceRejects.fieldNameRejected (afterDot := rem (rejectedSuffix boolean) 9) (span 11 12)
  · simp [TokenKindAbsentAt, TokenAt, rem, tokens, rejectedSuffix, sym]
  · simp [TokenKindAbsentAt, TokenAt, rem, tokens, rejectedSuffix, sym]
  · exact ⟨⟨by simp [rem, tokens, rejectedSuffix], rfl⟩, rfl⟩
  · cases boolean <;> simp [IdentifierAbsentAt, TokenAt, rem, tokens, rejectedSuffix, terminal, sym]
  · exact .reported (.token (current := terminal boolean) ⟨by simp [rem, tokens, rejectedSuffix], rfl⟩)

/-- The terminal identifier Failure is not appended to the earlier hyphen
event, including when the offending token is the Boolean keyword `true`. -/
theorem later_field_failure_preserves_prefix_only (boolean : Bool) (block : Parser Block) (prior : List ParseDiagnostic) :
    postfixTail literalExpression block 11 base (state (rejectedSuffix boolean) 0 prior) =
      .reject (terminalFailure boolean) (rejectedState boolean prior) ∧
    (rejectedState boolean prior).diagnostics = prior ++ [nameEvent] ∧
    (rejectedState boolean prior).peek? = some (terminal boolean) := by
  refine ⟨reject_of_trace block (input := state (rejectedSuffix boolean) 0 prior)
    (later_field_rejection boolean), ?_, rfl⟩
  simp only [rejectedState, State.diagnostics, List.reverse_cons, List.reverse_reverse]

/-- The raw Boolean name grammar succeeds here, but postfix field parsing uses
the stricter checked-identifier grammar and rejects the very same token. -/
theorem boolean_name_is_not_a_field_identifier :
    ExpressionNameTraceParses source 99 (rem (rejectedSuffix true) 9)
      { span := span 12 16, value := "true" } (rem (rejectedSuffix true) 10) [] ∧
    IdentifierAbsentAt (rem (rejectedSuffix true) 9) := by
  constructor
  · exact .boolean ⟨.trueKeyword ⟨by decide, rfl⟩, rfl⟩
  · simp [IdentifierAbsentAt, TokenAt, rem, tokens, rejectedSuffix, terminal]

theorem boundary_done_keeps_arbitrary_base_and_events (block : Parser Block) (value : Expr) (prior : List ParseDiagnostic) :
    postfixTail literalExpression block 2 value (state successfulSuffix 8 prior) =
      .ok value (state successfulSuffix 8 prior) :=
  success_of_trace block (input := state successfulSuffix 8 prior) (.done (by
    simp [PostfixSuffixAbsentAt, TokenKindAbsentAt, TokenAt, successfulSuffix, tokens, sym,
      state, State.declarativeRemainder]))

private def hidden (prior : List ParseDiagnostic) : State :=
  { state successfulSuffix 0 prior with window := { endIndex := 0, endByte := 99 } }
private def missing (prior : List ParseDiagnostic) : State :=
  { state successfulSuffix 0 prior with tokens := #[], window := { endIndex := 99, endByte := 99 } }

/-- A stored dot outside the visible window and an absent backing slot both
end the tail silently; neither authorizes consuming the hidden/unavailable dot. -/
theorem hidden_and_missing_suffixes_finish_silently (block : Parser Block) (prior : List ParseDiagnostic) :
    postfixTail literalExpression block 1 base (hidden prior) = .ok base (hidden prior) ∧
    postfixTail literalExpression block 100 base (missing prior) = .ok base (missing prior) ∧
    (hidden prior).tokens[0]? = some (sym 1 2 .dot) ∧ (hidden prior).peek? = none ∧
    (missing prior).atEnd = false ∧ (missing prior).peek? = none := by
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · exact success_of_trace block (input := hidden prior) (.done (by
      simp [PostfixSuffixAbsentAt, TokenKindAbsentAt, TokenAt, hidden, state, State.declarativeRemainder]))
  · exact success_of_trace block (input := missing prior) (.done (by
      simp [PostfixSuffixAbsentAt, TokenKindAbsentAt, TokenAt, missing, state, State.declarativeRemainder]))

end Solcore.Test.SyntaxPostfixTailTraceProperties
end
