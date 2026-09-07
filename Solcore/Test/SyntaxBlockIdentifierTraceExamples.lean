import Solcore.Test.SyntaxBlockIdentifierTraceContracts
import Solcore.Syntax.Parser.IsolatedBlockTraceCompletenessProperties

/-! Concrete token-carrier consumers of the test-only checked-name statement
parser. Independent derivations, not evaluation of a complete parser, determine
every AST, endpoint, and diagnostic. No canonical lexer claim is made here. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxBlockIdentifierTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxBlockIdentifierTraceContracts

private def source : SourceId := { origin := .main, path := "block-name-trace.sol" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def nameA : Identifier := { span := span 2 5, value := "a-b" }
private def nameC : Identifier := { span := span 6 9, value := "c-d" }
private def hyphen (name : Identifier) : ParseDiagnostic := {
  span := name.span, kind := .invalidIdentifierHyphen name.value
}
private def missing (name : Identifier) : ParseDiagnostic := {
  span := name.span, kind := .constraintViolation .expressionRequiresSemicolon
}
private def successTokens : Array Token := #[
  { span := span 0 1, value := .symbol .leftBrace },
  { span := nameA.span, value := .identifier nameA.value },
  { span := nameC.span, value := .identifier nameC.value },
  { span := span 10 11, value := .symbol .rightBrace }]
private def successRem (cursor : Nat) : Remainder := { tokens := successTokens, endIndex := 4, cursor }
private def successState (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "{ a-b c-d }" }
  tokens := successTokens, cursor := 0, window := { endIndex := 4, endByte := 11 }
  diagnosticsRev := prior.reverse
}
private def successBody : Block := {
  span := span 0 11, value := [nameStatement nameA, nameStatement nameC]
}

private theorem firstName : IdentifierTraceParses (successRem 1) nameA
    (successRem 2) [hyphen nameA] :=
  .parsed ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩ (.hyphen (by
    unfold IdentifierHyphenSpelling nameA; decide))

private theorem secondName : IdentifierTraceParses (successRem 2) nameC
    (successRem 3) [hyphen nameC] :=
  .parsed ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩ (.hyphen (by
    unfold IdentifierHyphenSpelling nameC; decide))

private theorem successItems (reportSource : SourceId) (endByte : Nat) :
    CoreBlockItemsTraceParses NameStatementTraceParses reportSource endByte (successRem 1)
      [nameStatement nameA, nameStatement nameC] (span 10 11) (successRem 4)
      [hyphen nameA, hyphen nameC] := by
  have closing : CoreBlockItemsTraceParses NameStatementTraceParses reportSource endByte
      (successRem 3) [] (span 10 11) (successRem 4) [] :=
    .close _ ⟨⟨by decide, rfl⟩, rfl⟩
  have last : CoreBlockItemsTraceParses NameStatementTraceParses reportSource endByte
      (successRem 2) [nameStatement nameC] (span 10 11) (successRem 4) [hyphen nameC] :=
    .next (by decide)
      (by simp [TokenKindAbsentAt, TokenAt, successRem, successTokens])
      (.parsed secondName) (by decide) closing
  exact .next (by decide)
    (by simp [TokenKindAbsentAt, TokenAt, successRem, successTokens])
    (.parsed firstName) (by decide) last

private theorem nameMissing (name : Identifier) :
    CoreBlockStatementDiagnosticTrace (nameStatement name) [missing name] :=
  .missing (fun impossible => impossible)

private theorem opening : ExactTokenParses (.symbol .leftBrace)
    (successRem 0) (span 0 1) (successRem 1) := ⟨⟨by decide, rfl⟩, rfl⟩

private theorem requireParsed (reportSource : SourceId) (endByte : Nat) :
    CoreBlockTraceParses NameStatementTraceParses .require reportSource endByte
      (successRem 0) successBody (successRem 4)
      [hyphen nameA, hyphen nameC, missing nameA, missing nameC] :=
  .parsed (span 0 1) (span 10 11) opening (successItems _ _)
    (.cons (nameMissing nameA) (.lastRequired (nameMissing nameC)))

private theorem allowParsed (reportSource : SourceId) (endByte : Nat) :
    CoreBlockTraceParses NameStatementTraceParses .allow reportSource endByte
      (successRem 0) successBody (successRem 4)
      [hyphen nameA, hyphen nameC, missing nameA] :=
  .parsed (span 0 1) (span 10 11) opening (successItems _ _)
    (.cons (nameMissing nameA) .lastAllowed)

/-- Both name events precede both full-statement termination events, after
every arbitrary prior event. The exact source-order block and endpoint agree. -/
theorem require_names_then_both_semicolons (prior : List ParseDiagnostic) :
    ∃ output, coreBlock checkedNameStatement .require (successState prior) = .ok successBody output ∧
      output.declarativeRemainder = successRem 4 ∧ output.diagnostics =
        prior ++ [hyphen nameA, hyphen nameC, missing nameA, missing nameC] := by
  simpa only [successState, State.diagnostics, List.reverse_reverse] using
    (coreBlock_trace_success_iff checkedNameStatement_success_sound
      checkedNameStatement_success_complete checkedNameStatement_success_context .require
      (input := successState prior)).mp (requireParsed _ _)

/-- Allowing a final expression removes only the last termination event;
both earlier checked-name events and the first missing semicolon remain. -/
theorem allow_names_then_first_semicolon (prior : List ParseDiagnostic) :
    ∃ output, coreBlock checkedNameStatement .allow (successState prior) = .ok successBody output ∧
      output.declarativeRemainder = successRem 4 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC, missing nameA] := by
  simpa only [successState, State.diagnostics, List.reverse_reverse] using
    (coreBlock_trace_success_iff checkedNameStatement_success_sound
      checkedNameStatement_success_complete checkedNameStatement_success_context .allow
      (input := successState prior)).mp (allowParsed _ _)

private def rejectionTokens : Array Token := #[
  { span := span 0 1, value := .symbol .leftBrace },
  { span := nameA.span, value := .identifier nameA.value },
  { span := span 6 7, value := .symbol .plus },
  { span := span 8 9, value := .symbol .rightBrace },
  { span := span 10 14, value := .identifier "tail" }]
private def rejectionRem (endIndex cursor : Nat) : Remainder := { tokens := rejectionTokens, endIndex, cursor }
private def rejectionState (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "{ a-b + } tail" }
  tokens := rejectionTokens, cursor := 0, window := { endIndex := 5, endByte := 14 }
  diagnosticsRev := prior.reverse
}
private def plusReport : ParseDiagnostic := {
  span := span 6 7
  kind := .unexpected (some (.symbol .plus)) { head := .identifier, tail := [] } .statement
}
private def capturedWindow : BalancedBlockCapture := {
  span := span 0 9, endIndex := 4, endByte := 9
}

private theorem rejectionParsed (policy : CoreBlockTailPolicy)
    (reportSource : SourceId) (endByte endIndex : Nat) (inside : 2 < endIndex) :
    CoreBlockTraceRejects NameStatementTraceParses NameStatementTraceRejects policy
      reportSource endByte (rejectionRem endIndex 0) (rejectionRem endIndex 2)
      plusReport [hyphen nameA] := by
  have nameParsed : NameStatementTraceParses reportSource endByte
      (rejectionRem endIndex 1) (nameStatement nameA) (rejectionRem endIndex 2) [hyphen nameA] :=
    .parsed (.parsed ⟨⟨by change 1 < endIndex; omega, rfl⟩, rfl, rfl, rfl⟩
      (.hyphen (by unfold IdentifierHyphenSpelling nameA; decide)))
  have rejected : NameStatementTraceRejects reportSource endByte
      (rejectionRem endIndex 2) (rejectionRem endIndex 2) plusReport [] :=
    ⟨.absent (by simp [IdentifierAbsentAt, TokenAt, rejectionRem, rejectionTokens]),
      .reported (.token (current := { span := span 6 7, value := .symbol .plus })
        ⟨inside, rfl⟩), rfl⟩
  have last : CoreBlockItemsTraceRejects NameStatementTraceParses NameStatementTraceRejects
      reportSource endByte (rejectionRem endIndex 2) (rejectionRem endIndex 2) plusReport [] :=
    .statementRejected inside
      (by simp [TokenKindAbsentAt, TokenAt, rejectionRem, rejectionTokens]) rejected
  have items : CoreBlockItemsTraceRejects NameStatementTraceParses NameStatementTraceRejects
      reportSource endByte (rejectionRem endIndex 1) (rejectionRem endIndex 2)
      plusReport [hyphen nameA] :=
    .laterRejected (by change 1 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, rejectionRem, rejectionTokens])
      nameParsed (by change 1 < 2; decide) last
  exact .itemsRejected (span 0 1)
    ⟨⟨by change 0 < endIndex; omega, rfl⟩, rfl⟩ items

private theorem balancedCapture : BalancedBlockCaptures (rejectionRem 5 0) capturedWindow :=
  .captured (input := rejectionRem 5 0) (openingSpan := span 0 1)
    (closingSpan := span 8 9) ⟨by decide, rfl⟩
    (.other (token := { span := nameA.span, value := .identifier nameA.value })
      ⟨by decide, rfl⟩ (by decide) (by decide)
      (.other (token := { span := span 6 7, value := .symbol .plus })
        ⟨by decide, rfl⟩ (by decide) (by decide)
        (.close ⟨by decide, rfl⟩)))

/-- Rejecting the plus leaves only the preceding name event under either
tail policy. No semicolon validation or final-report commit has happened. -/
theorem raw_rejection_keeps_only_name_event
    (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ failure output,
      coreBlock checkedNameStatement policy (rejectionState prior) = .reject failure output ∧
      output.declarativeRemainder = rejectionRem 5 2 ∧ failure.toDiagnostic = plusReport ∧
      output.diagnostics = prior ++ [hyphen nameA] := by
  simpa only [rejectionState, State.diagnostics, List.reverse_reverse] using
    (coreBlock_trace_reject_iff checkedNameStatement_success_sound checkedNameStatement_reject_sound
      checkedNameStatement_success_complete checkedNameStatement_reject_complete
      checkedNameStatement_success_context policy (input := rejectionState prior)).mp
      (rejectionParsed policy.declarative _ _ 5 (by decide))

/-- Captured rejection emits its report once after the name event, returns an
empty body, restores the full parent window, and leaves `tail` as the next token.
The child's byte boundary is 9 while the parent's remains 14. -/
theorem captured_rejection_preserves_tail
    (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output,
      isolateBlock (coreBlock checkedNameStatement policy) (rejectionState prior) =
        .ok { span := span 0 9, value := [] } output ∧
      output.declarativeRemainder = rejectionRem 5 4 ∧
      output.diagnostics = prior ++ [hyphen nameA, plusReport] ∧
      output.file = (rejectionState prior).file ∧
      output.window = (rejectionState prior).window ∧
      output.peek? = some { span := span 10 14, value := .identifier "tail" } := by
  have parsed : IsolatedBlockTraceParses
      (CoreBlockTraceParses NameStatementTraceParses policy.declarative)
      (CoreBlockTraceRejects NameStatementTraceParses NameStatementTraceRejects policy.declarative)
      source 14 (rejectionRem 5 0) { span := span 0 9, value := [] }
      (rejectionRem 5 4) [hyphen nameA, plusReport] :=
    .recovered balancedCapture (rejectionParsed policy.declarative source 9 4 (by decide))
  rcases isolateBlock_success_trace_complete
      (coreBlock_trace_success_complete checkedNameStatement_success_complete
        checkedNameStatement_success_context policy)
      (coreBlock_trace_reject_complete checkedNameStatement_success_complete
        checkedNameStatement_reject_complete checkedNameStatement_success_context policy)
      (input := rejectionState prior) parsed with ⟨output, result, after, diagnostics⟩
  rcases BlockInternals.captureBlock?_complete (input := rejectionState prior) balancedCapture with
    ⟨captured, captureResult, _, _, _⟩
  have frame := isolateBlock_captured_success_frame
    (input := rejectionState prior) captureResult result
  refine ⟨output, result, after, ?_, frame.1, frame.2.2.1, ?_⟩
  · simpa only [rejectionState, State.diagnostics, List.reverse_reverse] using diagnostics
  · have tokens := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = rejectionTokens at tokens
    change output.window.endIndex = 5 at endpoint
    change output.cursor = 4 at cursor
    simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
    rfl

end Solcore.Test.SyntaxBlockIdentifierTraceExamples
