import Solcore.Syntax.Parser.Expression
import Solcore.Syntax.CollectionValidity
import Solcore.Syntax.ExpressionValidity

/-! Provenance and state contracts for canonical Core expression layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ExpressionInternals

/-- Prefix unary scanning preserves operator spans and parser-state validity. -/
theorem unaryOperators_validFor :
    ∀ fuel operatorsRev input,
      input.ValidFor →
      List.ValidFor Located.ValidFor input.file operatorsRev →
      (unaryOperators fuel operatorsRev input).ValidFor input
        (List.ValidFor Located.ValidFor) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro operatorsRev input inputValid operatorsValid
      unfold unaryOperators
      cases found : input.peek? with
      | none =>
          exact ⟨by
            intro operator member
            exact operatorsValid operator (by simpa using member),
            inputValid, rfl⟩
      | some token =>
          cases decoded : unaryOp? token.value with
          | none =>
              simp only [decoded]
              exact ⟨by
                intro operator member
                exact operatorsValid operator (by simpa using member),
                inputValid, rfl⟩
          | some operator =>
              simp only [decoded]
              have advanced : input.advance? = some (token,
                  { input with cursor := input.cursor + 1 }) := by
                unfold State.advance?
                rw [found]
                rfl
              have nextValid := inputValid.advance?_validFor advanced
              have tokenValid := inputValid.peek?_span_validFor found
              have accumulatedValid : List.ValidFor Located.ValidFor
                  ({ input with cursor := input.cursor + 1 } : State).file
                  ({ span := token.span, value := operator } ::
                    operatorsRev) := by
                intro retained member
                rcases List.mem_cons.mp member with rfl | member
                · simpa only [Located.ValidFor] using tokenValid
                · simpa using operatorsValid retained member
              exact (inductionHypothesis
                ({ span := token.span, value := operator } :: operatorsRev)
                { input with cursor := input.cursor + 1 }
                nextValid accumulatedValid).of_file_eq rfl

/-- Prefix unary scanning preserves the complete immutable token window. -/
theorem unaryOperators_preservesTokenWindow (fuel : Nat)
    (operatorsRev : List (Located UnaryOp)) :
    Parser.PreservesTokenWindow (unaryOperators fuel operatorsRev) := by
  intro input
  induction fuel generalizing operatorsRev input with
  | zero => trivial
  | succ fuel inductionHypothesis =>
      unfold unaryOperators
      cases found : input.peek? with
      | none => exact ⟨rfl, rfl⟩
      | some token =>
          cases decoded : unaryOp? token.value with
          | none =>
              simp only [decoded]
              exact ⟨rfl, rfl⟩
          | some operator =>
              simp only [decoded]
              exact (inductionHypothesis
                ({ span := token.span, value := operator } :: operatorsRev)
                { input with cursor := input.cursor + 1 }).trans ⟨rfl, rfl⟩

theorem unaryOperators_preservesTokensOnSuccess (fuel : Nat)
    (operatorsRev : List (Located UnaryOp)) :
    Parser.PreservesTokensOnSuccess (unaryOperators fuel operatorsRev) :=
  (unaryOperators_preservesTokenWindow fuel
    operatorsRev).preservesTokensOnSuccess

/-- Prefix unary scanning never rewinds its input cursor. -/
theorem unaryOperators_cursorMonotoneOnSuccess (fuel : Nat)
    (operatorsRev : List (Located UnaryOp)) :
    Parser.CursorMonotoneOnSuccess (unaryOperators fuel operatorsRev) := by
  intro input operators next parsed
  induction fuel generalizing operatorsRev input with
  | zero => contradiction
  | succ fuel inductionHypothesis =>
      unfold unaryOperators at parsed
      cases found : input.peek? with
      | none =>
          simp only [found] at parsed
          cases parsed
          exact Nat.le_refl _
      | some token =>
          simp only [found] at parsed
          cases decoded : unaryOp? token.value with
          | none =>
              simp only [decoded] at parsed
              cases parsed
              exact Nat.le_refl _
          | some operator =>
              simp only [decoded] at parsed
              exact Nat.le_trans (by simp)
                (inductionHypothesis
                  ({ span := token.span, value := operator } :: operatorsRev)
                  { input with cursor := input.cursor + 1 } parsed)

/-- Unary wrapping preserves the final operand's source end. -/
theorem applyUnaryOperators_preservesBaseEnd
    (operators : List (Located UnaryOp)) (base : Expr) :
    (applyUnaryOperators operators base).span.endByte =
      base.span.endByte := by
  induction operators with
  | nil => rfl
  | cons operator rest inductionHypothesis =>
      simpa only [applyUnaryOperators, List.foldr, SourceSpan.cover] using
        inductionHypothesis

/-- Unary wrapping retains every operator and operand source range. -/
theorem applyUnaryOperators_validFor
    (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (operators : List (Located UnaryOp)) (base : Expr)
    (operatorsValid : List.ValidFor Located.ValidFor file operators)
    (baseValid : Expr.ValidFor statementValid file base)
    (ordered : ∀ operator ∈ operators,
      operator.span.startByte ≤ base.span.endByte) :
    Expr.ValidFor statementValid file
      (applyUnaryOperators operators base) := by
  induction operators with
  | nil => simpa only [applyUnaryOperators, List.foldr] using baseValid
  | cons operator rest inductionHypothesis =>
      have operatorValid : operator.span.ValidFor file := by
        simpa only [Located.ValidFor] using
          operatorsValid operator (by simp)
      have restValid : List.ValidFor Located.ValidFor file rest := by
        intro retained member
        exact operatorsValid retained (by simp [member])
      have restOrdered : ∀ retained ∈ rest,
          retained.span.startByte ≤ base.span.endByte := by
        intro retained member
        exact ordered retained (by simp [member])
      have operandValid := inductionHypothesis restValid restOrdered
      have outerValid := SourceSpan.cover_validFor operatorValid
        operandValid.span_valid (by
          rw [applyUnaryOperators_preservesBaseEnd]
          exact ordered operator (by simp))
      simpa only [applyUnaryOperators, List.foldr] using
        (Expr.ValidFor.unary outerValid operatorValid operandValid)

/-- Successful precedence lookup identifies the current token exactly. -/
theorem binaryAtPrecedence?_some_state_shape {input : State}
    {precedence : Nat} {operator : Located BinaryOp}
    (result : binaryAtPrecedence? input precedence = some operator) :
    ∃ token, input.peek? = some token ∧
      binaryOp? token.value = some operator.value ∧
      token.span = operator.span := by
  unfold binaryAtPrecedence? at result
  cases found : input.peek? with
  | none => simp [found] at result
  | some token =>
      simp only [found] at result
      cases decoded : binaryOp? token.value with
      | none => simp [decoded] at result
      | some value =>
          simp only [decoded] at result
          split at result
          · cases result
            exact ⟨token, rfl, by simpa using decoded, rfl⟩
          · contradiction

/-- Every recognized binary operator belongs to the active source. -/
theorem binaryAtPrecedence?_validFor {input : State}
    {precedence : Nat} {operator : Located BinaryOp}
    (inputValid : input.ValidFor)
    (result : binaryAtPrecedence? input precedence = some operator) :
    Located.ValidFor input.file operator := by
  rcases binaryAtPrecedence?_some_state_shape result with
    ⟨token, found, _decoded, span⟩
  simpa only [Located.ValidFor, ← span] using
    inputValid.peek?_span_validFor found

/-- Binary consumption is the exact one-token cursor update. -/
theorem consumeBinary_ok_state_shape (operator : Located BinaryOp)
    (input : State) :
    consumeBinary operator input =
      .ok () { input with cursor := input.cursor + 1 } := rfl

/-- Consuming a recognized current token preserves state validity. -/
theorem consumeBinary_reply_validFor (operator : Located BinaryOp)
    {input : State} (inputValid : input.ValidFor) {token : Token}
    (found : input.peek? = some token) :
    (consumeBinary operator input).ValidFor input (fun _ _ => True) := by
  unfold consumeBinary modifyState Reply.ValidFor
  refine ⟨trivial, ?_, rfl⟩
  apply inputValid.advance?_validFor (token := token)
  unfold State.advance?
  rw [found]
  rfl

/-- Binary consumption preserves the immutable token window. -/
theorem consumeBinary_preservesTokenWindow (operator : Located BinaryOp) :
    Parser.PreservesTokenWindow (consumeBinary operator) :=
  modifyState_preservesTokenWindow _ (fun _ => ⟨rfl, rfl⟩)

theorem consumeBinary_preservesTokensOnSuccess
    (operator : Located BinaryOp) :
    Parser.PreservesTokensOnSuccess (consumeBinary operator) :=
  (consumeBinary_preservesTokenWindow operator).preservesTokensOnSuccess

/-- Binary consumption advances the cursor by exactly one. -/
theorem consumeBinary_cursor_lt_onSuccess (operator : Located BinaryOp)
    {input final : State} {value : Unit}
    (result : consumeBinary operator input = .ok value final) :
    input.cursor < final.cursor := by
  unfold consumeBinary modifyState at result
  cases result
  simp

theorem consumeBinary_cursorMonotoneOnSuccess
    (operator : Located BinaryOp) :
    Parser.CursorMonotoneOnSuccess (consumeBinary operator) := by
  intro input value final result
  exact Nat.le_of_lt (consumeBinary_cursor_lt_onSuccess operator result)

/-- A binary node retains its two operands and operator provenance. -/
theorem binaryNode_validFor
    (statementValid : SourceFile → Statement → Prop) (file : SourceFile)
    (left : Expr) (operator : Located BinaryOp) (right : Expr)
    (leftValid : Expr.ValidFor statementValid file left)
    (operatorValid : Located.ValidFor file operator)
    (rightValid : Expr.ValidFor statementValid file right)
    (ordered : left.span.startByte ≤ right.span.endByte) :
    Expr.ValidFor statementValid file (binaryNode left operator right) := by
  unfold binaryNode
  exact Expr.ValidFor.binary
    (SourceSpan.cover_validFor leftValid.span_valid rightValid.span_valid ordered)
    leftValid (by simpa only [Located.ValidFor] using operatorValid) rightValid

@[simp] theorem binaryNode_startByte (left : Expr)
    (operator : Located BinaryOp) (right : Expr) :
    (binaryNode left operator right).span.startByte = left.span.startByte := rfl

@[simp] theorem binaryNode_endByte (left : Expr)
    (operator : Located BinaryOp) (right : Expr) :
    (binaryNode left operator right).span.endByte = right.span.endByte := rfl

/-- A left-associative tail preserves every ordinary token window. -/
theorem leftAssociativeTail_preservesTokenWindow (operand : Parser Expr)
    (operandWindow : Parser.PreservesTokenWindow operand)
    (precedence : Nat) : ∀ fuel left,
    Parser.PreservesTokenWindow
      (leftAssociativeTail operand precedence fuel left) := by
  intro fuel
  induction fuel with
  | zero =>
      intro left input
      trivial
  | succ fuel inductionHypothesis =>
      intro left input
      unfold leftAssociativeTail
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none => exact ⟨rfl, rfl⟩
      | some operator =>
          simp only
          have consumedShape := consumeBinary_preservesTokenWindow
            operator input
          cases consumedResult : consumeBinary operator input with
          | invariant error =>
              simp only
              trivial
          | reject failure rejected =>
              rw [consumedResult] at consumedShape
              simp only
              exact consumedShape
          | ok value afterOperator =>
              rw [consumedResult] at consumedShape
              simp only
              have operandShape := operandWindow afterOperator
              cases operandResult : operand afterOperator with
              | invariant error =>
                  simp only
                  trivial
              | reject failure rejected =>
                  rw [operandResult] at operandShape
                  simp only
                  exact operandShape.trans consumedShape
              | ok right next =>
                  rw [operandResult] at operandShape
                  simp only
                  exact (inductionHypothesis
                    (binaryNode left operator right) next).trans
                      (operandShape.trans consumedShape)

theorem leftAssociativeTail_preservesTokensOnSuccess
    (operand : Parser Expr)
    (operandWindow : Parser.PreservesTokenWindow operand)
    (precedence fuel : Nat) (left : Expr) :
    Parser.PreservesTokensOnSuccess
      (leftAssociativeTail operand precedence fuel left) :=
  (leftAssociativeTail_preservesTokenWindow operand operandWindow precedence
    fuel left).preservesTokensOnSuccess

/-- A left-associative tail never rewinds the parser cursor. -/
theorem leftAssociativeTail_cursorMonotoneOnSuccess
    (operand : Parser Expr)
    (operandCursor : Parser.CursorMonotoneOnSuccess operand)
    (precedence : Nat) : ∀ fuel left,
    Parser.CursorMonotoneOnSuccess
      (leftAssociativeTail operand precedence fuel left) := by
  intro fuel
  induction fuel with
  | zero =>
      intro left input expression final parsed
      contradiction
  | succ fuel inductionHypothesis =>
      intro left input expression final parsed
      unfold leftAssociativeTail at parsed
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none =>
          simp only [operatorResult] at parsed
          cases parsed
          exact Nat.le_refl _
      | some operator =>
          simp only [operatorResult] at parsed
          cases consumedResult : consumeBinary operator input with
          | invariant error => simp [consumedResult] at parsed
          | reject failure rejected => simp [consumedResult] at parsed
          | ok value afterOperator =>
              simp only [consumedResult] at parsed
              have consumedMonotone :=
                consumeBinary_cursorMonotoneOnSuccess operator input value
                  afterOperator consumedResult
              cases operandResult : operand afterOperator with
              | invariant error => simp [operandResult] at parsed
              | reject failure rejected => simp [operandResult] at parsed
              | ok right next =>
                  simp only [operandResult] at parsed
                  exact Nat.le_trans consumedMonotone
                    (Nat.le_trans
                      (operandCursor afterOperator right next operandResult)
                      (inductionHypothesis
                        (binaryNode left operator right) next expression final
                          parsed))

/-- Every successful left-associative tail keeps its original left edge. -/
theorem leftAssociativeTail_preservesLeftStartOnSuccess
    (operand : Parser Expr) (precedence : Nat) :
    ∀ fuel left input expression final,
      leftAssociativeTail operand precedence fuel left input =
        .ok expression final →
      expression.span.startByte = left.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro left input expression final parsed
      unfold leftAssociativeTail at parsed
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none =>
          simp only [operatorResult] at parsed
          cases parsed
          rfl
      | some operator =>
          simp only [operatorResult] at parsed
          cases consumedResult : consumeBinary operator input with
          | invariant error => simp [consumedResult] at parsed
          | reject failure rejected => simp [consumedResult] at parsed
          | ok value afterOperator =>
              simp only [consumedResult] at parsed
              cases operandResult : operand afterOperator with
              | invariant error => simp [operandResult] at parsed
              | reject failure rejected => simp [operandResult] at parsed
              | ok right next =>
                  simp only [operandResult] at parsed
                  simpa using inductionHypothesis
                    (binaryNode left operator right) next expression final
                      parsed

end ExpressionInternals
end Solcore.Syntax.Parser
