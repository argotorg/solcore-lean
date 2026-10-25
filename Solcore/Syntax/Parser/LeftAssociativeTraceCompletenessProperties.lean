import Solcore.Syntax.Parser.LeftAssociativeTraceSoundnessProperties

/-! Every finite independent left-associative tail derivation executes above
a derivation-dependent loop bound. Successful operands need only file/endByte
framing and may rewind or replace their numeric window and tokens. No bound by
remainingCount or completeness for the fixed-production whole layer follows. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

open DeclarativeGrammar

private theorem binary_none_of_absent {input : State} {precedence : Nat}
    (absent : BinaryOperatorAtPrecedenceAbsentAt precedence input.declarativeRemainder) :
    binaryAtPrecedence? input precedence = none := by
  cases selected : binaryAtPrecedence? input precedence with
  | none => rfl
  | some operator =>
      have parsed := consumeBinary_success_sound_of_binaryAtPrecedence?_some selected
        (consumeBinary_ok_state_shape operator input)
      exact False.elim (absent ⟨operator.span, operator.value, parsed.1, parsed.2.1⟩)

private theorem binary_some_of_parsed {input : State} {precedence : Nat} {after : Remainder}
    {operator : Located BinaryOp}
    (parsed : BinaryOperatorAtPrecedenceParses precedence input.declarativeRemainder operator after) :
    binaryAtPrecedence? input precedence = some operator := by
  rcases operator with ⟨operatorSpan, value⟩
  rcases parsed with ⟨operatorPrecedence, tokenAt, _⟩
  change input.cursor < input.window.endIndex ∧
    input.tokens[input.cursor]? = some { span := operatorSpan, value := .symbol value.symbol } at tokenAt
  have found : input.peek? = some { span := operatorSpan, value := .symbol value.symbol } := by
    unfold State.peek?
    rw [if_pos tokenAt.1, tokenAt.2]
  have decoded : binaryOp? (.symbol value.symbol) = some value := by cases value <;> rfl
  have selected : (value.precedence == precedence) = true := beq_iff_eq.mpr operatorPrecedence
  simp only [binaryAtPrecedence?, found, decoded, selected, if_true]

variable {operand : Parser Expr}
  {operandTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {operandRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

private theorem success_complete_at
    (successComplete : ParserTraceSuccessComplete operand operandTrace)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    {precedence : Nat} {source : SourceId} {endByte : Nat} {before after : Remainder}
    {left value : Expr} {trace : List ParseDiagnostic}
    (parsed : LeftAssociativeTailTraceParses operandTrace precedence source endByte before left value after trace) :
    ∀ input : State, input.file.id = source → input.window.endByte = endByte →
      input.declarativeRemainder = before →
      ∃ bound, ∀ fuel, bound ≤ fuel → ∃ output,
        leftAssociativeTail operand precedence fuel left input = .ok value output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  induction parsed with
  | done absent =>
      intro input sourceEq byteEq remEq
      cases sourceEq; cases byteEq; cases remEq
      refine ⟨1, ?_⟩
      intro fuel adequate
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact ⟨input, by simp only [leftAssociativeTail, binary_none_of_absent absent],
            rfl, (List.append_nil _).symm⟩
  | next operatorParsed rightParsed tail ih =>
      intro input sourceEq byteEq remEq
      cases sourceEq; cases byteEq; cases remEq
      have operatorResult := binary_some_of_parsed operatorParsed
      rcases operatorParsed with ⟨_, _, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) rightParsed with
        ⟨next, childResult, nextAfter, childEvents⟩
      have frame := successFrame childResult
      rcases ih next (congrArg SourceFile.id frame.1) frame.2 nextAfter with ⟨bound, tailComplete⟩
      refine ⟨bound + 1, ?_⟩
      intro fuel adequate
      cases fuel with
      | zero => omega
      | succ fuel =>
          rcases tailComplete fuel (by omega) with ⟨output, result, afterEq, events⟩
          refine ⟨output, ?_, afterEq, ?_⟩
          · simpa only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape, childResult,
              binaryNode, DeclarativeGrammar.binaryNode] using result
          · rw [events, childEvents]
            exact List.append_assoc _ _ _

private theorem reject_complete_at
    (successComplete : ParserTraceSuccessComplete operand operandTrace)
    (rejectComplete : ParserTraceRejectComplete operand operandRejects)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    {precedence : Nat} {source : SourceId} {endByte : Nat} {before after : Remainder}
    {left : Expr} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : LeftAssociativeTailTraceRejects operandTrace operandRejects precedence source endByte before left after report trace) :
    ∀ input : State, input.file.id = source → input.window.endByte = endByte →
      input.declarativeRemainder = before →
      ∃ bound, ∀ fuel, bound ≤ fuel → ∃ failure rejected,
        leftAssociativeTail operand precedence fuel left input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  induction rejection with
  | rightRejected operatorParsed rightRejected =>
      intro input sourceEq byteEq remEq
      cases sourceEq; cases byteEq; cases remEq
      have operatorResult := binary_some_of_parsed operatorParsed
      rcases operatorParsed with ⟨_, _, rfl⟩
      rcases rejectComplete (input := { input with cursor := input.cursor + 1 }) rightRejected with
        ⟨failure, rejected, childResult, afterEq, reportEq, events⟩
      refine ⟨1, ?_⟩
      intro fuel adequate
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact ⟨failure, rejected, by simp only [leftAssociativeTail, operatorResult,
            consumeBinary_ok_state_shape, childResult], afterEq, reportEq, events⟩
  | laterRejected operatorParsed rightParsed tail ih =>
      intro input sourceEq byteEq remEq
      cases sourceEq; cases byteEq; cases remEq
      have operatorResult := binary_some_of_parsed operatorParsed
      rcases operatorParsed with ⟨_, _, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) rightParsed with
        ⟨next, childResult, nextAfter, childEvents⟩
      have frame := successFrame childResult
      rcases ih next (congrArg SourceFile.id frame.1) frame.2 nextAfter with ⟨bound, tailComplete⟩
      refine ⟨bound + 1, ?_⟩
      intro fuel adequate
      cases fuel with
      | zero => omega
      | succ fuel =>
          rcases tailComplete fuel (by omega) with ⟨failure, rejected, result, afterEq, reportEq, events⟩
          refine ⟨failure, rejected, ?_, afterEq, reportEq, ?_⟩
          · simpa only [leftAssociativeTail, operatorResult, consumeBinary_ok_state_shape, childResult,
              binaryNode, DeclarativeGrammar.binaryNode] using result
          · rw [events, childEvents]
            exact List.append_assoc _ _ _

theorem leftAssociativeTail_trace_success_complete_eventually
    (successComplete : ParserTraceSuccessComplete operand operandTrace)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (precedence : Nat) {input : State} {left value : Expr} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : LeftAssociativeTailTraceParses operandTrace precedence input.file.id input.window.endByte
      input.declarativeRemainder left value after trace) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∃ output,
      leftAssociativeTail operand precedence fuel left input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  success_complete_at successComplete successFrame parsed input rfl rfl rfl

theorem leftAssociativeTail_trace_reject_complete_eventually
    (successComplete : ParserTraceSuccessComplete operand operandTrace)
    (rejectComplete : ParserTraceRejectComplete operand operandRejects)
    (successFrame : ∀ {input output value}, operand input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (precedence : Nat) {input : State} {left : Expr} {after : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : LeftAssociativeTailTraceRejects operandTrace operandRejects precedence input.file.id input.window.endByte
      input.declarativeRemainder left after report trace) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∃ failure rejected,
      leftAssociativeTail operand precedence fuel left input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  reject_complete_at successComplete rejectComplete successFrame rejection input rfl rfl rfl

end Solcore.Syntax.Parser.ExpressionInternals
