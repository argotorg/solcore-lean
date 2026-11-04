import Solcore.Syntax.Grammar.Expressions
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.Internal.ExpressionProofs
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Parser.Internal.CollectionSoundness
import Solcore.Syntax.Parser.Internal.DelimitedSoundness

/-!
Soundness of the parsers of binary, unary and conditional operators: each success and each
rejection has its declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionUnarySoundnessProperties
/-!
Diagnostic reflection and exact declarative soundness for prefix unary parsing.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

private theorem unaryOperatorAbsentAt_of_peek?_eq_none {input : State}
    (found : input.peek? = none) :
    DeclarativeGrammar.UnaryOperatorAbsentAt input.declarativeRemainder := by
  constructor <;> rintro ⟨span, inside, tokenFound⟩
  all_goals
    have cursorInside : input.cursor < input.window.endIndex := by
      simpa [State.declarativeRemainder] using inside
    have lookup := tokenFound
    simp only [State.declarativeRemainder] at lookup
    unfold State.peek? at found
    rw [if_pos cursorInside, lookup] at found
    contradiction

private theorem unaryOperatorAbsentAt_of_unaryOp?_eq_none
    {input : State} {token : Token}
    (found : input.peek? = some token)
    (decoded : unaryOp? token.value = none) :
    DeclarativeGrammar.UnaryOperatorAbsentAt input.declarativeRemainder := by
  constructor
  · rintro ⟨span, _inside, tokenFound⟩
    have currentFound := (tokenAt_of_peek?_eq_some found).2
    have same : token = { span, value := TokenKind.symbol .bang } :=
      Option.some.inj (currentFound.symm.trans tokenFound)
    subst token
    simp [unaryOp?] at decoded
  · rintro ⟨span, _inside, tokenFound⟩
    have currentFound := (tokenAt_of_peek?_eq_some found).2
    have same : token = { span, value := TokenKind.symbol .tilde } :=
      Option.some.inj (currentFound.symm.trans tokenFound)
    subst token
    simp [unaryOp?] at decoded

private theorem unaryOperator_success_sound {input : State} {token : Token}
    {operator : UnaryOp}
    (found : input.peek? = some token)
    (decoded : unaryOp? token.value = some operator) :
    DeclarativeGrammar.UnaryOperatorParses input.declarativeRemainder
      { span := token.span, value := operator }
      ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder := by
  unfold DeclarativeGrammar.UnaryOperatorParses
  unfold DeclarativeGrammar.ExactTokenParses
  refine ⟨?_, rfl⟩
  rcases token with ⟨span, kind⟩
  cases kind <;> simp [unaryOp?] at decoded
  case symbol symbol =>
    cases symbol <;> simp at decoded
    all_goals cases decoded
    all_goals simpa [UnaryOp.symbol, State.declarativeRemainder] using
      tokenAt_of_peek?_eq_some found

private theorem unaryOperators_success_sound_from_accumulator :
    ∀ fuel operatorsRev input operators next,
      unaryOperators fuel operatorsRev input = .ok operators next →
      ∃ suffix,
        operators = operatorsRev.reverse ++ suffix ∧
          DeclarativeGrammar.UnaryOperatorsParses
            input.declarativeRemainder suffix next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro operatorsRev input operators next result
      unfold unaryOperators at result
      cases found : input.peek? with
      | none =>
          simp only [found] at result
          cases result
          exact ⟨[], by simp,
            .done (unaryOperatorAbsentAt_of_peek?_eq_none found)⟩
      | some token =>
          simp only [found] at result
          cases decoded : unaryOp? token.value with
          | none =>
              simp only [decoded] at result
              cases result
              exact ⟨[], by simp,
                .done (unaryOperatorAbsentAt_of_unaryOp?_eq_none found
                  decoded)⟩
          | some operator =>
              simp only [decoded] at result
              rcases inductionHypothesis
                  ({ span := token.span, value := operator } :: operatorsRev)
                  { input with cursor := input.cursor + 1 }
                  operators next result with
                ⟨suffix, output, tail⟩
              exact ⟨{ span := token.span, value := operator } :: suffix,
                by simpa [List.reverse_cons, List.append_assoc] using output,
                .next (unaryOperator_success_sound found decoded) tail⟩

/--
Every successful initial unary scan consumes exactly the maximal source-order
operator sequence, including the stopping-token absence evidence.
-/
theorem unaryOperators_success_sound {fuel : Nat} {input next : State}
    {operators : List (Located UnaryOp)}
    (result : unaryOperators fuel [] input = .ok operators next) :
    DeclarativeGrammar.UnaryOperatorsParses input.declarativeRemainder
      operators next.declarativeRemainder := by
  rcases unaryOperators_success_sound_from_accumulator fuel [] input operators
      next result with ⟨suffix, output, grammar⟩
  simp only [List.reverse_nil, List.nil_append] at output
  subst operators
  exact grammar

/-- Prefix unary scanning never removes an earlier diagnostic. -/
theorem unaryOperators_reflectsDiagnosticFreeOnSuccess
    (fuel : Nat) (operatorsRev : List (Located UnaryOp)) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (unaryOperators fuel operatorsRev) := by
  induction fuel generalizing operatorsRev with
  | zero => intro input operators next result; contradiction
  | succ fuel inductionHypothesis =>
      intro input operators next result diagnosticFree
      unfold unaryOperators at result
      cases found : input.peek? with
      | none => simp only [found] at result; cases result; exact diagnosticFree
      | some token =>
          simp only [found] at result
          cases decoded : unaryOp? token.value with
          | none =>
              simp only [decoded] at result
              cases result
              exact diagnosticFree
          | some operator =>
              simp only [decoded] at result
              exact inductionHypothesis
                ({ span := token.span, value := operator } :: operatorsRev)
                { input with cursor := input.cursor + 1 }
                operators next result diagnosticFree

/-- Unary-layer success reflects through its scanner and postfix operand. -/
theorem expressionUnary_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (postfixReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionPostfix nested block)) :
    Parser.ReflectsDiagnosticFreeOnSuccess (expressionUnary nested block) := by
  intro input expression next result diagnosticFree
  unfold expressionUnary at result
  cases operatorsResult : unaryOperators (input.remainingCount + 1) [] input with
  | reject failure rejected => simp [operatorsResult] at result
  | invariant error => simp [operatorsResult] at result
  | ok operators afterOperators =>
      simp only [operatorsResult] at result
      cases postfixResult : expressionPostfix nested block afterOperators with
      | reject failure rejected => simp [postfixResult] at result
      | invariant error => simp [postfixResult] at result
      | ok base afterPostfix =>
          simp only [postfixResult] at result
          cases result
          have afterOperatorsFree := postfixReflects afterOperators base next
            postfixResult diagnosticFree
          exact unaryOperators_reflectsDiagnosticFreeOnSuccess
            (input.remainingCount + 1) [] input operators afterOperators
              operatorsResult afterOperatorsFree

private theorem applyUnaryOperators_eq_declarative
    (operators : List (Located UnaryOp)) (base : Expr) :
    applyUnaryOperators operators base =
      DeclarativeGrammar.applyUnaryOperators operators base := by
  rfl

/--
Every diagnostic-free unary-layer success follows the maximal prefix grammar
and the supplied postfix grammar exactly.
-/
theorem expressionUnary_success_sound
    (nested : Parser Expr) (block : Parser Block)
    (postfixParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (postfixReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionPostfix nested block))
    (postfixSound : ∀ {postfixInput postfixNext : State} {base : Expr},
      postfixNext.diagnosticsRev = [] →
      expressionPostfix nested block postfixInput = .ok base postfixNext →
      postfixParses postfixInput.declarativeRemainder base
        postfixNext.declarativeRemainder)
    {input next : State} {expression : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : expressionUnary nested block input = .ok expression next) :
    DeclarativeGrammar.ExpressionUnaryParses postfixParses
      input.declarativeRemainder expression next.declarativeRemainder := by
  unfold expressionUnary at result
  cases operatorsResult : unaryOperators (input.remainingCount + 1) [] input with
  | reject failure rejected => simp [operatorsResult] at result
  | invariant error => simp [operatorsResult] at result
  | ok operators afterOperators =>
      simp only [operatorsResult] at result
      cases postfixResult : expressionPostfix nested block afterOperators with
      | reject failure rejected => simp [postfixResult] at result
      | invariant error => simp [postfixResult] at result
      | ok base afterPostfix =>
          simp only [postfixResult] at result
          cases result
          have afterOperatorsFree := postfixReflects afterOperators base next
            postfixResult diagnosticFree
          exact ⟨operators, afterOperators.declarativeRemainder, base,
            unaryOperators_success_sound operatorsResult,
            postfixSound diagnosticFree postfixResult,
            applyUnaryOperators_eq_declarative operators base⟩

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionBinaryOperatorSoundnessProperties
/-!
Exact declarative bridges for Core binary-operator lookahead and consumption.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- Successful precedence lookahead records the selected precedence exactly. -/
theorem binaryAtPrecedence?_some_precedence {input : State}
    {precedence : Nat} {operator : Located BinaryOp}
    (result : binaryAtPrecedence? input precedence = some operator) :
    operator.value.precedence = precedence :=
  (binaryAtPrecedence?_some_state_shape result).choose_spec.2.2.1

/--
A successful lookup followed by consumption is one exact declarative binary
operator transition.
-/
theorem consumeBinary_success_sound_of_binaryAtPrecedence?_some
    {input next : State} {precedence : Nat}
    {operator : Located BinaryOp}
    (recognized : binaryAtPrecedence? input precedence = some operator)
    (consumed : consumeBinary operator input = .ok () next) :
    DeclarativeGrammar.BinaryOperatorAtPrecedenceParses precedence
      input.declarativeRemainder operator next.declarativeRemainder := by
  rcases binaryAtPrecedence?_some_state_shape recognized with
    ⟨_token, _found, decoded, precedenceEq, _bound⟩
  rw [consumeBinary_ok_state_shape operator input] at consumed
  cases consumed
  exact ⟨precedenceEq, decoded, rfl⟩

/-- Failed precedence lookahead excludes that exact operator class. -/
theorem binaryAtPrecedence?_none_absentAt {input : State}
    {precedence : Nat}
    (result : binaryAtPrecedence? input precedence = none) :
    DeclarativeGrammar.BinaryOperatorAtPrecedenceAbsentAt precedence
      input.declarativeRemainder := by
  rintro ⟨operator, operatorPrecedence, decoded⟩
  have found : BinaryOp.at? input.tokens input.window.endIndex input.cursor =
      some operator := decoded
  unfold binaryAtPrecedence? at result
  rw [found] at result
  have selected : (operator.value.precedence == precedence) = true :=
    beq_iff_eq.mpr operatorPrecedence
  simp only [selected, if_true] at result
  contradiction

/-- Binary consumption preserves the diagnostic stack exactly on success. -/
theorem consumeBinary_reflectsDiagnosticFreeOnSuccess
    (operator : Located BinaryOp) :
    Parser.ReflectsDiagnosticFreeOnSuccess (consumeBinary operator) := by
  intro input value next result diagnosticFree
  unfold consumeBinary modifyState at result
  cases result
  exact diagnosticFree

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionBinaryLayerSoundnessProperties
/-!
Parametric diagnostic reflection and strict declarative soundness for Core
left-associative and non-associative binary precedence layers.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- A left-associative tail cannot erase an incoming diagnostic. -/
theorem leftAssociativeTail_reflectsDiagnosticFreeOnSuccess
    (operand : Parser Expr)
    (operandReflects : Parser.ReflectsDiagnosticFreeOnSuccess operand)
    (precedence : Nat) :
    ∀ fuel left,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (leftAssociativeTail operand precedence fuel left) := by
  intro fuel
  induction fuel with
  | zero =>
      intro left input expression next result diagnosticFree
      simp [leftAssociativeTail] at result
  | succ fuel inductionHypothesis =>
      intro left input expression next result diagnosticFree
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none =>
          simp only [leftAssociativeTail, operatorResult] at result
          cases result
          exact diagnosticFree
      | some operator =>
          let afterOperator := { input with cursor := input.cursor + operator.value.tokenCount }
          have consumedResult :
              consumeBinary operator input = .ok () afterOperator :=
            consumeBinary_ok_state_shape operator input
          cases operandResult : operand afterOperator with
          | invariant error =>
              simp [leftAssociativeTail, operatorResult, consumedResult,
                operandResult] at result
          | reject failure rejected =>
              simp [leftAssociativeTail, operatorResult, consumedResult,
                operandResult] at result
          | ok right afterRight =>
              simp only [leftAssociativeTail, operatorResult, consumedResult,
                operandResult] at result
              have afterRightFree := inductionHypothesis
                (binaryNode left operator right) afterRight expression next
                  result diagnosticFree
              have afterOperatorFree := operandReflects afterOperator right
                afterRight operandResult afterRightFree
              exact consumeBinary_reflectsDiagnosticFreeOnSuccess operator
                input () afterOperator consumedResult afterOperatorFree

/-- A complete left-associative layer reflects diagnostic freedom. -/
theorem leftAssociative_reflectsDiagnosticFreeOnSuccess
    (operand : Parser Expr)
    (operandReflects : Parser.ReflectsDiagnosticFreeOnSuccess operand)
    (precedence : Nat) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (leftAssociative operand precedence) := by
  intro input expression next result diagnosticFree
  unfold leftAssociative at result
  cases operandResult : operand input with
  | invariant error => simp [operandResult] at result
  | reject failure rejected => simp [operandResult] at result
  | ok left afterLeft =>
      simp only [operandResult] at result
      have afterLeftFree :=
        leftAssociativeTail_reflectsDiagnosticFreeOnSuccess operand
          operandReflects precedence (afterLeft.remainingCount + 1) left
            afterLeft expression next result diagnosticFree
      exact operandReflects input left afterLeft operandResult afterLeftFree

/--
Every diagnostic-free successful left-associative tail is maximal and follows
the exact declarative operator/operand sequence.
-/
theorem leftAssociativeTail_success_sound
    (operand : Parser Expr)
    (operandParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (operandReflects : Parser.ReflectsDiagnosticFreeOnSuccess operand)
    (operandSound : ∀ {input next : State} {expression : Expr},
      next.diagnosticsRev = [] →
      operand input = .ok expression next →
      operandParses input.declarativeRemainder expression
        next.declarativeRemainder)
    (precedence : Nat) :
    ∀ fuel left input expression next,
      next.diagnosticsRev = [] →
      leftAssociativeTail operand precedence fuel left input =
        .ok expression next →
      DeclarativeGrammar.LeftAssociativeTailParses operandParses precedence
        input.declarativeRemainder left expression next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro left input expression next diagnosticFree result
      simp [leftAssociativeTail] at result
  | succ fuel inductionHypothesis =>
      intro left input expression next diagnosticFree result
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none =>
          simp only [leftAssociativeTail, operatorResult] at result
          cases result
          exact .done (binaryAtPrecedence?_none_absentAt operatorResult)
      | some operator =>
          let afterOperator := { input with cursor := input.cursor + operator.value.tokenCount }
          have consumedResult :
              consumeBinary operator input = .ok () afterOperator :=
            consumeBinary_ok_state_shape operator input
          cases operandResult : operand afterOperator with
          | invariant error =>
              simp [leftAssociativeTail, operatorResult, consumedResult,
                operandResult] at result
          | reject failure rejected =>
              simp [leftAssociativeTail, operatorResult, consumedResult,
                operandResult] at result
          | ok right afterRight =>
              simp only [leftAssociativeTail, operatorResult, consumedResult,
                operandResult] at result
              have tailGrammar := inductionHypothesis
                (binaryNode left operator right) afterRight expression next
                  diagnosticFree result
              have afterRightFree :=
                leftAssociativeTail_reflectsDiagnosticFreeOnSuccess operand
                  operandReflects precedence fuel
                    (binaryNode left operator right) afterRight expression next
                      result diagnosticFree
              have rightGrammar := operandSound afterRightFree operandResult
              have operatorGrammar :=
                consumeBinary_success_sound_of_binaryAtPrecedence?_some
                  operatorResult consumedResult
              apply DeclarativeGrammar.LeftAssociativeTailParses.next
                operatorGrammar rightGrammar
              simpa only [binaryNode, DeclarativeGrammar.binaryNode] using
                tailGrammar

/-- Every diagnostic-free complete left-associative success is sound. -/
theorem leftAssociative_success_sound
    (operand : Parser Expr)
    (operandParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (operandReflects : Parser.ReflectsDiagnosticFreeOnSuccess operand)
    (operandSound : ∀ {input next : State} {expression : Expr},
      next.diagnosticsRev = [] →
      operand input = .ok expression next →
      operandParses input.declarativeRemainder expression
        next.declarativeRemainder)
    (precedence : Nat) {input next : State} {expression : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : leftAssociative operand precedence input = .ok expression next) :
    DeclarativeGrammar.LeftAssociativeParses operandParses precedence
      input.declarativeRemainder expression next.declarativeRemainder := by
  unfold leftAssociative at result
  cases operandResult : operand input with
  | invariant error => simp [operandResult] at result
  | reject failure rejected => simp [operandResult] at result
  | ok left afterLeft =>
      simp only [operandResult] at result
      have afterLeftFree :=
        leftAssociativeTail_reflectsDiagnosticFreeOnSuccess operand
          operandReflects precedence (afterLeft.remainingCount + 1) left
            afterLeft expression next result diagnosticFree
      exact ⟨left, afterLeft.declarativeRemainder,
        operandSound afterLeftFree operandResult,
        leftAssociativeTail_success_sound operand operandParses operandReflects
          operandSound precedence (afterLeft.remainingCount + 1) left afterLeft
            expression next diagnosticFree result⟩

/-- A non-associative binary layer cannot erase an incoming diagnostic. -/
theorem nonAssociative_reflectsDiagnosticFreeOnSuccess
    (operand : Parser Expr)
    (operandReflects : Parser.ReflectsDiagnosticFreeOnSuccess operand)
    (precedence : Nat) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (nonAssociative operand precedence) := by
  intro input expression next result diagnosticFree
  unfold nonAssociative at result
  cases leftResult : operand input with
  | invariant error => simp [leftResult] at result
  | reject failure rejected => simp [leftResult] at result
  | ok left afterLeft =>
      simp only [leftResult] at result
      cases operatorResult : binaryAtPrecedence? afterLeft precedence with
      | none =>
          simp only [operatorResult] at result
          cases result
          exact operandReflects input expression next leftResult diagnosticFree
      | some operator =>
          let afterOperator := { afterLeft with
            cursor := afterLeft.cursor + operator.value.tokenCount }
          have consumedResult :
              consumeBinary operator afterLeft = .ok () afterOperator :=
            consumeBinary_ok_state_shape operator afterLeft
          cases rightResult : operand afterOperator with
          | invariant error =>
              simp [operatorResult, consumedResult, rightResult] at result
          | reject failure rejected =>
              simp [operatorResult, consumedResult, rightResult] at result
          | ok right final =>
              simp only [operatorResult, consumedResult, rightResult] at result
              cases result
              have afterOperatorFree := operandReflects afterOperator right
                next rightResult diagnosticFree
              have afterLeftFree :=
                consumeBinary_reflectsDiagnosticFreeOnSuccess operator
                  afterLeft () afterOperator consumedResult afterOperatorFree
              exact operandReflects input left afterLeft leftResult
                afterLeftFree

/-- Every diagnostic-free non-associative success follows its exact grammar. -/
theorem nonAssociative_success_sound
    (operand : Parser Expr)
    (operandParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (operandReflects : Parser.ReflectsDiagnosticFreeOnSuccess operand)
    (operandSound : ∀ {input next : State} {expression : Expr},
      next.diagnosticsRev = [] →
      operand input = .ok expression next →
      operandParses input.declarativeRemainder expression
        next.declarativeRemainder)
    (precedence : Nat) {input next : State} {expression : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : nonAssociative operand precedence input = .ok expression next) :
    DeclarativeGrammar.NonAssociativeParses operandParses precedence
      input.declarativeRemainder expression next.declarativeRemainder := by
  unfold nonAssociative at result
  cases leftResult : operand input with
  | invariant error => simp [leftResult] at result
  | reject failure rejected => simp [leftResult] at result
  | ok left afterLeft =>
      simp only [leftResult] at result
      cases operatorResult : binaryAtPrecedence? afterLeft precedence with
      | none =>
          simp only [operatorResult] at result
          cases result
          exact .plain (operandSound diagnosticFree leftResult)
            (binaryAtPrecedence?_none_absentAt operatorResult)
      | some operator =>
          let afterOperator := { afterLeft with
            cursor := afterLeft.cursor + operator.value.tokenCount }
          have consumedResult :
              consumeBinary operator afterLeft = .ok () afterOperator :=
            consumeBinary_ok_state_shape operator afterLeft
          cases rightResult : operand afterOperator with
          | invariant error =>
              simp [operatorResult, consumedResult, rightResult] at result
          | reject failure rejected =>
              simp [operatorResult, consumedResult, rightResult] at result
          | ok right final =>
              simp only [operatorResult, consumedResult, rightResult] at result
              cases result
              have afterOperatorFree := operandReflects afterOperator right
                next rightResult diagnosticFree
              have afterLeftFree :=
                consumeBinary_reflectsDiagnosticFreeOnSuccess operator
                  afterLeft () afterOperator consumedResult afterOperatorFree
              have parsed : DeclarativeGrammar.NonAssociativeParses
                  operandParses precedence input.declarativeRemainder
                    (DeclarativeGrammar.binaryNode left operator right)
                      next.declarativeRemainder :=
                .binary (operandSound afterLeftFree leftResult)
                  (consumeBinary_success_sound_of_binaryAtPrecedence?_some
                    operatorResult consumedResult)
                  (operandSound diagnosticFree rightResult)
              simpa only [binaryNode, DeclarativeGrammar.binaryNode] using parsed

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionNonAssociativeOrdinaryOutcomeSoundnessProperties
/-!
Executable ordinary-success and exact-rejection bridges for one Core
non-associative binary precedence layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- Every executable non-associative success is either an operator-absent
plain operand or one exact binary node. -/
theorem nonAssociative_success_ordinary_sound
    (operand : Parser Expr)
    (operandOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (operandSuccessSound : ∀ {input output : State} {expression : Expr},
      operand input = .ok expression output →
        operandOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (precedence : Nat) {input output : State} {expression : Expr}
    (result : nonAssociative operand precedence input =
      .ok expression output) :
    DeclarativeGrammar.NonAssociativeOrdinaryParses operandOrdinary precedence
      input.declarativeRemainder expression output.declarativeRemainder := by
  unfold nonAssociative at result
  cases leftResult : operand input with
  | invariant error => simp [leftResult] at result
  | reject failure rejected => simp [leftResult] at result
  | ok left afterLeft =>
      simp only [leftResult] at result
      cases operatorResult : binaryAtPrecedence? afterLeft precedence with
      | none =>
          simp only [operatorResult] at result
          cases result
          exact .plain (operandSuccessSound leftResult)
            (binaryAtPrecedence?_none_absentAt operatorResult)
      | some operator =>
          let afterOperator := { afterLeft with
            cursor := afterLeft.cursor + operator.value.tokenCount }
          have consumedResult :
              consumeBinary operator afterLeft = .ok () afterOperator :=
            consumeBinary_ok_state_shape operator afterLeft
          cases rightResult : operand afterOperator with
          | invariant error =>
              simp [operatorResult, consumedResult, rightResult] at result
          | reject failure rejected =>
              simp [operatorResult, consumedResult, rightResult] at result
          | ok right final =>
              simp only [operatorResult, consumedResult, rightResult] at result
              cases result
              have parsed : DeclarativeGrammar.NonAssociativeOrdinaryParses
                  operandOrdinary precedence input.declarativeRemainder
                    (DeclarativeGrammar.binaryNode left operator right)
                      output.declarativeRemainder :=
                .binary (operandSuccessSound leftResult)
                  (consumeBinary_success_sound_of_binaryAtPrecedence?_some
                    operatorResult consumedResult)
                  (operandSuccessSound rightResult)
              simpa only [binaryNode, DeclarativeGrammar.binaryNode] using
                parsed

/-- Every executable non-associative rejection is the first operand or the
right operand after an exact selected operator. -/
theorem nonAssociative_reject_ordinary_sound
    (operand : Parser Expr)
    (operandOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (operandRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (operandSuccessSound : ∀ {input output : State} {expression : Expr},
      operand input = .ok expression output →
        operandOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (operandRejectSound : ∀ {input rejected : State} {failure : Failure},
      operand input = .reject failure rejected →
        operandRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (precedence : Nat) {input rejected : State} {failure : Failure}
    (result : nonAssociative operand precedence input =
      .reject failure rejected) :
    DeclarativeGrammar.NonAssociativeRejects operandOrdinary operandRejects
      precedence input.declarativeRemainder rejected.declarativeRemainder := by
  unfold nonAssociative at result
  cases leftResult : operand input with
  | invariant error => simp [leftResult] at result
  | reject operandFailure operandRejected =>
      simp only [leftResult] at result
      cases result
      exact .firstRejected (operandRejectSound leftResult)
  | ok left afterLeft =>
      simp only [leftResult] at result
      cases operatorResult : binaryAtPrecedence? afterLeft precedence with
      | none => simp [operatorResult] at result
      | some operator =>
          let afterOperator := { afterLeft with
            cursor := afterLeft.cursor + operator.value.tokenCount }
          have consumedResult :
              consumeBinary operator afterLeft = .ok () afterOperator :=
            consumeBinary_ok_state_shape operator afterLeft
          cases rightResult : operand afterOperator with
          | invariant error =>
              simp [operatorResult, consumedResult, rightResult] at result
          | ok right final =>
              simp [operatorResult, consumedResult, rightResult] at result
          | reject rightFailure rightRejected =>
              simp only [operatorResult, consumedResult, rightResult] at result
              cases result
              exact .rightRejected (operandSuccessSound leftResult)
                (consumeBinary_success_sound_of_binaryAtPrecedence?_some
                  operatorResult consumedResult)
                (operandRejectSound rightResult)

/-- Package both executable non-associative outcomes. -/
theorem nonAssociative_ordinaryOutcome_sound
    (operand : Parser Expr)
    (operandOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (operandRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (operandSuccessSound : ∀ {input output : State} {expression : Expr},
      operand input = .ok expression output →
        operandOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (operandRejectSound : ∀ {input rejected : State} {failure : Failure},
      operand input = .reject failure rejected →
        operandRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (precedence : Nat) :
    (∀ {input output : State} {expression : Expr},
      nonAssociative operand precedence input = .ok expression output →
        DeclarativeGrammar.NonAssociativeOrdinaryParses operandOrdinary
          precedence input.declarativeRemainder expression
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      nonAssociative operand precedence input = .reject failure rejected →
        DeclarativeGrammar.NonAssociativeRejects operandOrdinary operandRejects
          precedence input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨nonAssociative_success_ordinary_sound operand operandOrdinary
      operandSuccessSound precedence,
    nonAssociative_reject_ordinary_sound operand operandOrdinary operandRejects
      operandSuccessSound operandRejectSound precedence⟩

/-- Lift a deterministic operand contract through one non-associative layer. -/
theorem nonAssociative_ordinaryOutcomeSpec
    {operandOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {operandRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (outcomes : DeclarativeGrammar.DeterministicOutcomeSpec operandOrdinary
      operandRejects) (precedence : Nat) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.NonAssociativeOrdinaryParses operandOrdinary
        precedence)
      (DeclarativeGrammar.NonAssociativeRejects operandOrdinary operandRejects
        precedence) :=
  DeclarativeGrammar.nonAssociativeDeterministicOutcomeSpec outcomes precedence

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionLeftAssociativeOrdinaryOutcomeSoundnessProperties
/-!
Executable ordinary-success and exact-rejection bridges for one Core
left-associative binary precedence layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- Every executable left-associative tail success follows the maximal
operator/operand sequence at the selected precedence. -/
theorem leftAssociativeTail_success_ordinary_sound
    (operand : Parser Expr)
    (operandOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (operandSuccessSound : ∀ {input output : State} {expression : Expr},
      operand input = .ok expression output →
        operandOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (precedence : Nat) :
    ∀ fuel left input expression output,
      leftAssociativeTail operand precedence fuel left input =
          .ok expression output →
        DeclarativeGrammar.LeftAssociativeTailParses operandOrdinary
          precedence input.declarativeRemainder left expression
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro left input expression output result
      simp [leftAssociativeTail] at result
  | succ fuel inductionHypothesis =>
      intro left input expression output result
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none =>
          simp only [leftAssociativeTail, operatorResult] at result
          cases result
          exact .done (binaryAtPrecedence?_none_absentAt operatorResult)
      | some operator =>
          let afterOperator := { input with cursor := input.cursor + operator.value.tokenCount }
          have consumedResult :
              consumeBinary operator input = .ok () afterOperator :=
            consumeBinary_ok_state_shape operator input
          cases operandResult : operand afterOperator with
          | invariant error =>
              simp [leftAssociativeTail, operatorResult, consumedResult,
                operandResult] at result
          | reject failure rejected =>
              simp [leftAssociativeTail, operatorResult, consumedResult,
                operandResult] at result
          | ok right afterRight =>
              simp only [leftAssociativeTail, operatorResult, consumedResult,
                operandResult] at result
              have tailParsed := inductionHypothesis
                (binaryNode left operator right) afterRight expression output
                  result
              apply DeclarativeGrammar.LeftAssociativeTailParses.next
                (consumeBinary_success_sound_of_binaryAtPrecedence?_some
                  operatorResult consumedResult)
                (operandSuccessSound operandResult)
              simpa only [binaryNode, DeclarativeGrammar.binaryNode] using
                tailParsed

/-- Every executable left-associative tail rejection records the exact first
rejected right operand or a rejection in a later suffix. -/
theorem leftAssociativeTail_reject_ordinary_sound
    (operand : Parser Expr)
    (operandOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (operandRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (operandSuccessSound : ∀ {input output : State} {expression : Expr},
      operand input = .ok expression output →
        operandOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (operandRejectSound : ∀ {input rejected : State} {failure : Failure},
      operand input = .reject failure rejected →
        operandRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (precedence : Nat) :
    ∀ fuel left input rejected failure,
      leftAssociativeTail operand precedence fuel left input =
          .reject failure rejected →
        DeclarativeGrammar.LeftAssociativeTailRejects operandOrdinary
          operandRejects precedence input.declarativeRemainder left
            rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro left input rejected failure result
      simp [leftAssociativeTail] at result
  | succ fuel inductionHypothesis =>
      intro left input rejected failure result
      cases operatorResult : binaryAtPrecedence? input precedence with
      | none =>
          simp [leftAssociativeTail, operatorResult] at result
      | some operator =>
          let afterOperator := { input with cursor := input.cursor + operator.value.tokenCount }
          have consumedResult :
              consumeBinary operator input = .ok () afterOperator :=
            consumeBinary_ok_state_shape operator input
          have operatorParsed :=
            consumeBinary_success_sound_of_binaryAtPrecedence?_some
              operatorResult consumedResult
          cases operandResult : operand afterOperator with
          | invariant error =>
              simp [leftAssociativeTail, operatorResult, consumedResult,
                operandResult] at result
          | reject operandFailure operandRejected =>
              simp only [leftAssociativeTail, operatorResult, consumedResult,
                operandResult] at result
              cases result
              exact .rightRejected operatorParsed
                (operandRejectSound operandResult)
          | ok right afterRight =>
              simp only [leftAssociativeTail, operatorResult, consumedResult,
                operandResult] at result
              have tailRejected := inductionHypothesis
                (binaryNode left operator right) afterRight rejected failure
                  result
              apply DeclarativeGrammar.LeftAssociativeTailRejects.laterRejected
                operatorParsed (operandSuccessSound operandResult)
              simpa only [binaryNode, DeclarativeGrammar.binaryNode] using
                tailRejected

/-- Every executable complete left-associative success follows its ordinary
first operand and maximal operator tail. -/
theorem leftAssociative_success_ordinary_sound
    (operand : Parser Expr)
    (operandOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (operandSuccessSound : ∀ {input output : State} {expression : Expr},
      operand input = .ok expression output →
        operandOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (precedence : Nat) {input output : State} {expression : Expr}
    (result : leftAssociative operand precedence input =
      .ok expression output) :
    DeclarativeGrammar.LeftAssociativeOrdinaryParses operandOrdinary
      precedence input.declarativeRemainder expression
        output.declarativeRemainder := by
  unfold leftAssociative at result
  cases operandResult : operand input with
  | invariant error => simp [operandResult] at result
  | reject failure rejected => simp [operandResult] at result
  | ok left afterLeft =>
      simp only [operandResult] at result
      exact ⟨left, afterLeft.declarativeRemainder,
        operandSuccessSound operandResult,
        leftAssociativeTail_success_ordinary_sound operand operandOrdinary
          operandSuccessSound precedence (afterLeft.remainingCount + 1) left
            afterLeft expression output result⟩

/-- Every executable complete left-associative rejection is the first operand
rejection or an exact rejection in its maximal operator tail. -/
theorem leftAssociative_reject_ordinary_sound
    (operand : Parser Expr)
    (operandOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (operandRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (operandSuccessSound : ∀ {input output : State} {expression : Expr},
      operand input = .ok expression output →
        operandOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (operandRejectSound : ∀ {input rejected : State} {failure : Failure},
      operand input = .reject failure rejected →
        operandRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (precedence : Nat) {input rejected : State} {failure : Failure}
    (result : leftAssociative operand precedence input =
      .reject failure rejected) :
    DeclarativeGrammar.LeftAssociativeRejects operandOrdinary operandRejects
      precedence input.declarativeRemainder rejected.declarativeRemainder := by
  unfold leftAssociative at result
  cases operandResult : operand input with
  | invariant error => simp [operandResult] at result
  | reject operandFailure operandRejected =>
      simp only [operandResult] at result
      cases result
      exact .firstRejected (operandRejectSound operandResult)
  | ok left afterLeft =>
      simp only [operandResult] at result
      exact .tailRejected (operandSuccessSound operandResult)
        (leftAssociativeTail_reject_ordinary_sound operand operandOrdinary
          operandRejects operandSuccessSound operandRejectSound precedence
            (afterLeft.remainingCount + 1) left afterLeft rejected failure
              result)

/-- Package both executable outcomes for one supplied operand bridge. -/
theorem leftAssociative_ordinaryOutcome_sound
    (operand : Parser Expr)
    (operandOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (operandRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (operandSuccessSound : ∀ {input output : State} {expression : Expr},
      operand input = .ok expression output →
        operandOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (operandRejectSound : ∀ {input rejected : State} {failure : Failure},
      operand input = .reject failure rejected →
        operandRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (precedence : Nat) :
    (∀ {input output : State} {expression : Expr},
      leftAssociative operand precedence input = .ok expression output →
        DeclarativeGrammar.LeftAssociativeOrdinaryParses operandOrdinary
          precedence input.declarativeRemainder expression
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      leftAssociative operand precedence input = .reject failure rejected →
        DeclarativeGrammar.LeftAssociativeRejects operandOrdinary
          operandRejects precedence input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨leftAssociative_success_ordinary_sound operand operandOrdinary
      operandSuccessSound precedence,
    leftAssociative_reject_ordinary_sound operand operandOrdinary
      operandRejects operandSuccessSound operandRejectSound precedence⟩

/-- Lift a deterministic operand contract through one precedence layer. -/
theorem leftAssociative_ordinaryOutcomeSpec
    {operandOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {operandRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (outcomes : DeclarativeGrammar.DeterministicOutcomeSpec operandOrdinary
      operandRejects) (precedence : Nat) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.LeftAssociativeOrdinaryParses operandOrdinary
        precedence)
      (DeclarativeGrammar.LeftAssociativeRejects operandOrdinary
        operandRejects precedence) :=
  DeclarativeGrammar.leftAssociativeDeterministicOutcomeSpec outcomes
    precedence

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionConditionalSoundnessProperties
/-!
Diagnostic reflection and declarative soundness for the generic conditional
expression layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- The fuel-bounded conditional tail never removes an earlier diagnostic. -/
theorem conditionalTail_reflectsDiagnosticFreeOnSuccess
    (nested alternative : Parser Expr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (alternativeReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess alternative) :
    ∀ fuel headsRev condition,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (conditionalTail nested alternative fuel headsRev condition) := by
  intro fuel
  induction fuel with
  | zero =>
      intro headsRev condition input value next result diagnosticFree
      simp [conditionalTail] at result
  | succ fuel inductionHypothesis =>
      intro headsRev condition input value next result diagnosticFree
      unfold conditionalTail at result
      split at result
      · cases questionResult : symbol .question .expression input with
        | invariant error => simp [questionResult] at result
        | reject failure rejected => simp [questionResult] at result
        | ok question afterQuestion =>
            simp only [questionResult] at result
            cases thenResult : nested afterQuestion with
            | invariant error => simp [thenResult] at result
            | reject failure rejected => simp [thenResult] at result
            | ok thenBranch afterThen =>
                simp only [thenResult] at result
                cases colonResult : symbol .colon .expression afterThen with
                | invariant error => simp [colonResult] at result
                | reject failure rejected => simp [colonResult] at result
                | ok colon afterColon =>
                    simp only [colonResult] at result
                    cases alternativeResult : alternative afterColon with
                    | invariant error => simp [alternativeResult] at result
                    | reject failure rejected =>
                        simp [alternativeResult] at result
                    | ok nextCondition afterAlternative =>
                        simp only [alternativeResult] at result
                        have afterAlternativeFree := inductionHypothesis
                          ({
                            condition
                            question := question.span
                            thenBranch
                            colon := colon.span
                          } :: headsRev) nextCondition afterAlternative value
                            next result diagnosticFree
                        have afterColonFree := alternativeReflects afterColon
                          nextCondition afterAlternative alternativeResult
                            afterAlternativeFree
                        have afterThenFree :=
                          symbol_reflectsDiagnosticFreeOnSuccess .colon
                            .expression afterThen colon afterColon colonResult
                              afterColonFree
                        have afterQuestionFree := nestedReflects afterQuestion
                          thenBranch afterThen thenResult afterThenFree
                        exact symbol_reflectsDiagnosticFreeOnSuccess .question
                          .expression input question afterQuestion questionResult
                            afterQuestionFree
      · cases result
        exact diagnosticFree

/-- Public conditional parsing reflects through its first alternative. -/
theorem conditional_reflectsDiagnosticFreeOnSuccess
    (nested alternative : Parser Expr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (alternativeReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess alternative) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (conditional nested alternative) := by
  intro input value next result diagnosticFree
  unfold conditional at result
  cases alternativeResult : alternative input with
  | invariant error => simp [alternativeResult] at result
  | reject failure rejected => simp [alternativeResult] at result
  | ok condition afterCondition =>
      simp only [alternativeResult] at result
      have afterConditionFree :=
        conditionalTail_reflectsDiagnosticFreeOnSuccess nested alternative
          nestedReflects alternativeReflects
            (afterCondition.remainingCount + 1) [] condition afterCondition
              value next result diagnosticFree
      exact alternativeReflects input condition afterCondition
        alternativeResult afterConditionFree

private theorem conditionalTail_success_sound_strong
    (nested alternative : Parser Expr)
    (nestedParses alternativeParses :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
        nestedParses input.declarativeRemainder value
          next.declarativeRemainder)
    (alternativeReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess alternative)
    (alternativeSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → alternative input = .ok value next →
        alternativeParses input.declarativeRemainder value
          next.declarativeRemainder) :
    ∀ fuel headsRev condition input value next,
      next.diagnosticsRev = [] →
      conditionalTail nested alternative fuel headsRev condition input =
          .ok value next →
      ∃ tailExpression,
        value = headsRev.foldl foldConditionalHead tailExpression ∧
        DeclarativeGrammar.ConditionalTailParses nestedParses
          alternativeParses input.declarativeRemainder condition tailExpression
            next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro headsRev condition input value next diagnosticFree result
      simp [conditionalTail] at result
  | succ fuel inductionHypothesis =>
      intro headsRev condition input value next diagnosticFree result
      unfold conditionalTail at result
      split at result
      next questionPresent =>
        cases questionResult : symbol .question .expression input with
        | invariant error => simp [questionResult] at result
        | reject failure rejected => simp [questionResult] at result
        | ok question afterQuestion =>
            simp only [questionResult] at result
            cases thenResult : nested afterQuestion with
            | invariant error => simp [thenResult] at result
            | reject failure rejected => simp [thenResult] at result
            | ok thenBranch afterThen =>
                simp only [thenResult] at result
                cases colonResult : symbol .colon .expression afterThen with
                | invariant error => simp [colonResult] at result
                | reject failure rejected => simp [colonResult] at result
                | ok colon afterColon =>
                    simp only [colonResult] at result
                    cases alternativeResult : alternative afterColon with
                    | invariant error => simp [alternativeResult] at result
                    | reject failure rejected =>
                        simp [alternativeResult] at result
                    | ok nextCondition afterAlternative =>
                        simp only [alternativeResult] at result
                        let head : ConditionalHead := {
                          condition
                          question := question.span
                          thenBranch
                          colon := colon.span
                        }
                        rcases inductionHypothesis (head :: headsRev)
                            nextCondition afterAlternative value next
                              diagnosticFree result with
                          ⟨tailExpression, valueEq, tailGrammar⟩
                        have afterAlternativeFree :=
                          conditionalTail_reflectsDiagnosticFreeOnSuccess
                            nested alternative nestedReflects
                              alternativeReflects fuel (head :: headsRev)
                                nextCondition afterAlternative value next result
                                  diagnosticFree
                        have afterColonFree := alternativeReflects afterColon
                          nextCondition afterAlternative alternativeResult
                            afterAlternativeFree
                        have afterThenFree :=
                          symbol_reflectsDiagnosticFreeOnSuccess .colon
                            .expression afterThen colon afterColon colonResult
                              afterColonFree
                        have nestedGrammar := nestedSound afterThenFree
                          thenResult
                        have alternativeGrammar := alternativeSound
                          afterAlternativeFree alternativeResult
                        refine ⟨foldConditionalHead tailExpression head, ?_, ?_⟩
                        · simpa [head] using valueEq
                        · simpa [head, foldConditionalHead] using
                            (DeclarativeGrammar.ConditionalTailParses.next
                              question.span colon.span
                              (symbol_success_exactTokenParses .question
                                .expression questionResult)
                              nestedGrammar
                              (symbol_success_exactTokenParses .colon
                                .expression colonResult)
                              alternativeGrammar tailGrammar)
      next questionAbsent =>
        cases result
        refine ⟨condition, rfl, .done ?_⟩
        exact symbolAbsentAt_of_isSymbol_eq_false .question
          (Bool.eq_false_iff.mpr questionAbsent)

/-- Every diagnostic-free conditional success follows the exact right fold. -/
theorem conditional_success_sound
    (nested alternative : Parser Expr)
    (nestedParses alternativeParses :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
        nestedParses input.declarativeRemainder value
          next.declarativeRemainder)
    (alternativeReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess alternative)
    (alternativeSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → alternative input = .ok value next →
        alternativeParses input.declarativeRemainder value
          next.declarativeRemainder)
    {input next : State} {value : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : conditional nested alternative input = .ok value next) :
    DeclarativeGrammar.ConditionalParses nestedParses alternativeParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold conditional at result
  cases alternativeResult : alternative input with
  | invariant error => simp [alternativeResult] at result
  | reject failure rejected => simp [alternativeResult] at result
  | ok condition afterCondition =>
      simp only [alternativeResult] at result
      have afterConditionFree :=
        conditionalTail_reflectsDiagnosticFreeOnSuccess nested alternative
          nestedReflects alternativeReflects
            (afterCondition.remainingCount + 1) [] condition afterCondition
              value next result diagnosticFree
      have conditionGrammar := alternativeSound afterConditionFree
        alternativeResult
      rcases conditionalTail_success_sound_strong nested alternative
          nestedParses alternativeParses nestedReflects nestedSound
            alternativeReflects alternativeSound
              (afterCondition.remainingCount + 1) [] condition afterCondition
                value next diagnosticFree result with
        ⟨tailExpression, valueEq, tailGrammar⟩
      simp only [List.foldl_nil] at valueEq
      subst value
      exact ⟨condition, afterCondition.declarativeRemainder,
        conditionGrammar, tailGrammar⟩

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionLayerSoundnessProperties
/-!
Aggregate diagnostic reflection and exact declarative soundness for one Core
expression recursion layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A complete expression layer reflects diagnostic freedom through every
precedence layer and its supplied recursive and postfix parsers. -/
theorem expressionLayer_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (postfixReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionPostfix nested block)) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionLayer nested block) := by
  let unary := ExpressionInternals.expressionUnary nested block
  let multiply := ExpressionInternals.leftAssociative unary 9
  let add := ExpressionInternals.leftAssociative multiply 8
  let shift := ExpressionInternals.leftAssociative add 7
  let bitAnd := ExpressionInternals.leftAssociative shift 6
  let bitXor := ExpressionInternals.leftAssociative bitAnd 5
  let bitOr := ExpressionInternals.leftAssociative bitXor 4
  let relational := ExpressionInternals.nonAssociative bitOr 3
  let equality := ExpressionInternals.nonAssociative relational 2
  let logicalAnd := ExpressionInternals.leftAssociative equality 1
  let logicalOr := ExpressionInternals.leftAssociative logicalAnd 0
  have unaryReflects : Parser.ReflectsDiagnosticFreeOnSuccess unary :=
    ExpressionInternals.expressionUnary_reflectsDiagnosticFreeOnSuccess
      nested block postfixReflects
  have multiplyReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess multiply :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      unary unaryReflects 9
  have addReflects : Parser.ReflectsDiagnosticFreeOnSuccess add :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      multiply multiplyReflects 8
  have shiftReflects : Parser.ReflectsDiagnosticFreeOnSuccess shift :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      add addReflects 7
  have bitAndReflects : Parser.ReflectsDiagnosticFreeOnSuccess bitAnd :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      shift shiftReflects 6
  have bitXorReflects : Parser.ReflectsDiagnosticFreeOnSuccess bitXor :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      bitAnd bitAndReflects 5
  have bitOrReflects : Parser.ReflectsDiagnosticFreeOnSuccess bitOr :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      bitXor bitXorReflects 4
  have relationalReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess relational :=
    ExpressionInternals.nonAssociative_reflectsDiagnosticFreeOnSuccess
      bitOr bitOrReflects 3
  have equalityReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess equality :=
    ExpressionInternals.nonAssociative_reflectsDiagnosticFreeOnSuccess
      relational relationalReflects 2
  have logicalAndReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess logicalAnd :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      equality equalityReflects 1
  have logicalOrReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess logicalOr :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      logicalAnd logicalAndReflects 0
  exact ExpressionInternals.conditional_reflectsDiagnosticFreeOnSuccess
    nested logicalOr nestedReflects logicalOrReflects

/-- Every diagnostic-free successful expression layer follows the exact
parser-independent unary, precedence, associativity, and conditional grammar. -/
theorem expressionLayer_success_sound
    (nested : Parser Expr) (block : Parser Block)
    (nestedParses postfixParses :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
        nestedParses input.declarativeRemainder value
          next.declarativeRemainder)
    (postfixReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionPostfix nested block))
    (postfixSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] →
        expressionPostfix nested block input =
          .ok value next →
        postfixParses input.declarativeRemainder value
          next.declarativeRemainder)
    {input next : State} {value : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : expressionLayer nested block input = .ok value next) :
    DeclarativeGrammar.ExpressionLayerParses nestedParses postfixParses
      input.declarativeRemainder value next.declarativeRemainder := by
  let unary := ExpressionInternals.expressionUnary nested block
  let multiply := ExpressionInternals.leftAssociative unary 9
  let add := ExpressionInternals.leftAssociative multiply 8
  let shift := ExpressionInternals.leftAssociative add 7
  let bitAnd := ExpressionInternals.leftAssociative shift 6
  let bitXor := ExpressionInternals.leftAssociative bitAnd 5
  let bitOr := ExpressionInternals.leftAssociative bitXor 4
  let relational := ExpressionInternals.nonAssociative bitOr 3
  let equality := ExpressionInternals.nonAssociative relational 2
  let logicalAnd := ExpressionInternals.leftAssociative equality 1
  let logicalOr := ExpressionInternals.leftAssociative logicalAnd 0
  let unaryParses :=
    DeclarativeGrammar.ExpressionUnaryParses postfixParses
  let multiplyParses :=
    DeclarativeGrammar.LeftAssociativeParses unaryParses 9
  let addParses :=
    DeclarativeGrammar.LeftAssociativeParses multiplyParses 8
  let shiftParses :=
    DeclarativeGrammar.LeftAssociativeParses addParses 7
  let bitAndParses :=
    DeclarativeGrammar.LeftAssociativeParses shiftParses 6
  let bitXorParses :=
    DeclarativeGrammar.LeftAssociativeParses bitAndParses 5
  let bitOrParses :=
    DeclarativeGrammar.LeftAssociativeParses bitXorParses 4
  let relationalParses :=
    DeclarativeGrammar.NonAssociativeParses bitOrParses 3
  let equalityParses :=
    DeclarativeGrammar.NonAssociativeParses relationalParses 2
  let logicalAndParses :=
    DeclarativeGrammar.LeftAssociativeParses equalityParses 1
  let logicalOrParses :=
    DeclarativeGrammar.LeftAssociativeParses logicalAndParses 0
  have unaryReflects : Parser.ReflectsDiagnosticFreeOnSuccess unary :=
    ExpressionInternals.expressionUnary_reflectsDiagnosticFreeOnSuccess
      nested block postfixReflects
  have unarySound : ∀ {layerInput layerNext : State} {expression : Expr},
      layerNext.diagnosticsRev = [] →
      unary layerInput = .ok expression layerNext →
      unaryParses layerInput.declarativeRemainder expression
        layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.expressionUnary_success_sound
      nested block postfixParses postfixReflects postfixSound
        layerFree layerResult
  have multiplyReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess multiply :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      unary unaryReflects 9
  have multiplySound :
      ∀ {layerInput layerNext : State} {expression : Expr},
        layerNext.diagnosticsRev = [] →
        multiply layerInput = .ok expression layerNext →
        multiplyParses layerInput.declarativeRemainder expression
          layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.leftAssociative_success_sound
      unary unaryParses unaryReflects unarySound 9 layerFree layerResult
  have addReflects : Parser.ReflectsDiagnosticFreeOnSuccess add :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      multiply multiplyReflects 8
  have addSound : ∀ {layerInput layerNext : State} {expression : Expr},
      layerNext.diagnosticsRev = [] →
      add layerInput = .ok expression layerNext →
      addParses layerInput.declarativeRemainder expression
        layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.leftAssociative_success_sound
      multiply multiplyParses multiplyReflects multiplySound 8
        layerFree layerResult
  have shiftReflects : Parser.ReflectsDiagnosticFreeOnSuccess shift :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      add addReflects 7
  have bitAndReflects : Parser.ReflectsDiagnosticFreeOnSuccess bitAnd :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      shift shiftReflects 6
  have shiftSound : ∀ {layerInput layerNext : State} {expression : Expr},
      layerNext.diagnosticsRev = [] →
      shift layerInput = .ok expression layerNext →
      shiftParses layerInput.declarativeRemainder expression
        layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.leftAssociative_success_sound
      add addParses addReflects addSound 7 layerFree layerResult
  have bitAndSound : ∀ {layerInput layerNext : State} {expression : Expr},
      layerNext.diagnosticsRev = [] →
      bitAnd layerInput = .ok expression layerNext →
      bitAndParses layerInput.declarativeRemainder expression
        layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.leftAssociative_success_sound
      shift shiftParses shiftReflects shiftSound 6 layerFree layerResult
  have bitXorReflects : Parser.ReflectsDiagnosticFreeOnSuccess bitXor :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      bitAnd bitAndReflects 5
  have bitXorSound : ∀ {layerInput layerNext : State} {expression : Expr},
      layerNext.diagnosticsRev = [] →
      bitXor layerInput = .ok expression layerNext →
      bitXorParses layerInput.declarativeRemainder expression
        layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.leftAssociative_success_sound
      bitAnd bitAndParses bitAndReflects bitAndSound 5 layerFree layerResult
  have bitOrReflects : Parser.ReflectsDiagnosticFreeOnSuccess bitOr :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      bitXor bitXorReflects 4
  have bitOrSound : ∀ {layerInput layerNext : State} {expression : Expr},
      layerNext.diagnosticsRev = [] →
      bitOr layerInput = .ok expression layerNext →
      bitOrParses layerInput.declarativeRemainder expression
        layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.leftAssociative_success_sound
      bitXor bitXorParses bitXorReflects bitXorSound 4 layerFree layerResult
  have relationalReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess relational :=
    ExpressionInternals.nonAssociative_reflectsDiagnosticFreeOnSuccess
      bitOr bitOrReflects 3
  have relationalSound :
      ∀ {layerInput layerNext : State} {expression : Expr},
        layerNext.diagnosticsRev = [] →
        relational layerInput = .ok expression layerNext →
        relationalParses layerInput.declarativeRemainder expression
          layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.nonAssociative_success_sound
      bitOr bitOrParses bitOrReflects bitOrSound 3 layerFree layerResult
  have equalityReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess equality :=
    ExpressionInternals.nonAssociative_reflectsDiagnosticFreeOnSuccess
      relational relationalReflects 2
  have equalitySound :
      ∀ {layerInput layerNext : State} {expression : Expr},
        layerNext.diagnosticsRev = [] →
        equality layerInput = .ok expression layerNext →
        equalityParses layerInput.declarativeRemainder expression
          layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.nonAssociative_success_sound
      relational relationalParses relationalReflects relationalSound 2
        layerFree layerResult
  have logicalAndReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess logicalAnd :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      equality equalityReflects 1
  have logicalAndSound :
      ∀ {layerInput layerNext : State} {expression : Expr},
        layerNext.diagnosticsRev = [] →
        logicalAnd layerInput = .ok expression layerNext →
        logicalAndParses layerInput.declarativeRemainder expression
          layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.leftAssociative_success_sound
      equality equalityParses equalityReflects equalitySound 1
        layerFree layerResult
  have logicalOrReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess logicalOr :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      logicalAnd logicalAndReflects 0
  have logicalOrSound :
      ∀ {layerInput layerNext : State} {expression : Expr},
        layerNext.diagnosticsRev = [] →
        logicalOr layerInput = .ok expression layerNext →
        logicalOrParses layerInput.declarativeRemainder expression
          layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.leftAssociative_success_sound
      logicalAnd logicalAndParses logicalAndReflects logicalAndSound 0
        layerFree layerResult
  exact ExpressionInternals.conditional_success_sound
    nested logicalOr nestedParses logicalOrParses nestedReflects nestedSound
      logicalOrReflects logicalOrSound diagnosticFree result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionStepSoundnessProperties
/-!
Aggregate diagnostic reflection and exact soundness for one complete Core
expression recursion step.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- One complete expression step reflects diagnostic freedom through its
supplied atom and recursive expression parsers. -/
theorem expressionStep_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (atomReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionAtom nested block))
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionLayer nested block) :=
  expressionLayer_reflectsDiagnosticFreeOnSuccess nested block
    nestedReflects
    (expressionPostfix_reflectsDiagnosticFreeOnSuccess nested block
      atomReflects nestedReflects)

/-- Diagnostic-free success of one complete expression step follows the
parser-independent atom/postfix/precedence/conditional composition. -/
theorem expressionStep_success_sound
    (nested : Parser Expr) (block : Parser Block)
    (atomParses nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (atomReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionAtom nested block))
    (atomSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] →
      expressionAtom nested block input = .ok value next →
      atomParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value
        next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {value : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : expressionLayer nested block input =
      .ok value next) :
    DeclarativeGrammar.CoreExpressionStepParses atomParses nestedParses
      input.declarativeRemainder value next.declarativeRemainder := by
  let postfixParses :=
    DeclarativeGrammar.ExpressionPostfixParses atomParses nestedParses
  have postfixReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionPostfix nested block) :=
    expressionPostfix_reflectsDiagnosticFreeOnSuccess nested block
      atomReflects nestedReflects
  have postfixSound : ∀ {postfixInput postfixNext : State}
      {expression : Expr},
      postfixNext.diagnosticsRev = [] →
      expressionPostfix nested block postfixInput =
        .ok expression postfixNext →
      postfixParses postfixInput.declarativeRemainder expression
        postfixNext.declarativeRemainder := by
    intro postfixInput postfixNext expression postfixFree postfixResult
    exact expressionPostfix_success_sound nested block atomParses nestedParses
      atomSound nestedReflects nestedSound nestedShape postfixFree
        postfixResult
  exact expressionLayer_success_sound nested block nestedParses postfixParses
    nestedReflects nestedSound postfixReflects postfixSound diagnosticFree
      result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionConditionalOrdinarySuccessSoundnessProperties
/-!
Unconditional ordinary-success bridges for the Core conditional expression
layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- Every executable conditional-tail success decomposes into the outstanding
head fold and an exact right-associated ordinary conditional tail. -/
theorem conditionalTail_success_ordinary_sound_strong
    (nested alternative : Parser Expr)
    (nestedOrdinary alternativeOrdinary :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output →
        nestedOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (alternativeSuccessSound :
      ∀ {input output : State} {expression : Expr},
        alternative input = .ok expression output →
          alternativeOrdinary input.declarativeRemainder expression
            output.declarativeRemainder) :
    ∀ fuel headsRev condition input expression output,
      conditionalTail nested alternative fuel headsRev condition input =
          .ok expression output →
        ∃ tailExpression,
          expression = headsRev.foldl foldConditionalHead tailExpression ∧
          DeclarativeGrammar.ConditionalTailParses nestedOrdinary
            alternativeOrdinary input.declarativeRemainder condition
              tailExpression output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro headsRev condition input expression output result
      simp [conditionalTail] at result
  | succ fuel inductionHypothesis =>
      intro headsRev condition input expression output result
      unfold conditionalTail at result
      split at result
      next questionPresent =>
        cases questionResult : symbol .question .expression input with
        | invariant error => simp [questionResult] at result
        | reject failure rejected => simp [questionResult] at result
        | ok question afterQuestion =>
            simp only [questionResult] at result
            cases thenResult : nested afterQuestion with
            | invariant error => simp [thenResult] at result
            | reject failure rejected => simp [thenResult] at result
            | ok thenBranch afterThen =>
                simp only [thenResult] at result
                cases colonResult : symbol .colon .expression afterThen with
                | invariant error => simp [colonResult] at result
                | reject failure rejected => simp [colonResult] at result
                | ok colon afterColon =>
                    simp only [colonResult] at result
                    cases alternativeResult : alternative afterColon with
                    | invariant error => simp [alternativeResult] at result
                    | reject failure rejected =>
                        simp [alternativeResult] at result
                    | ok nextCondition afterAlternative =>
                        simp only [alternativeResult] at result
                        let head : ConditionalHead := {
                          condition
                          question := question.span
                          thenBranch
                          colon := colon.span
                        }
                        rcases inductionHypothesis (head :: headsRev)
                            nextCondition afterAlternative expression output
                              result with
                          ⟨tailExpression, expressionEq, tailParsed⟩
                        have parsed :=
                          DeclarativeGrammar.ConditionalTailParses.next
                            (condition := condition)
                            question.span colon.span
                            (symbol_success_exactTokenParses .question
                              .expression questionResult)
                            (nestedSuccessSound thenResult)
                            (symbol_success_exactTokenParses .colon
                              .expression colonResult)
                            (alternativeSuccessSound alternativeResult)
                            tailParsed
                        refine ⟨foldConditionalHead tailExpression head,
                          ?_, ?_⟩
                        · simpa [head] using expressionEq
                        · simpa [head, foldConditionalHead] using parsed
      next questionAbsent =>
        cases result
        refine ⟨condition, rfl, .done ?_⟩
        exact symbolAbsentAt_of_isSymbol_eq_false .question
          (Bool.eq_false_iff.mpr questionAbsent)

/-- Every complete executable conditional success follows the exact ordinary
right-associated conditional grammar, independently of diagnostics. -/
theorem conditional_success_ordinary_sound
    (nested alternative : Parser Expr)
    (nestedOrdinary alternativeOrdinary :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output →
        nestedOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (alternativeSuccessSound :
      ∀ {input output : State} {expression : Expr},
        alternative input = .ok expression output →
          alternativeOrdinary input.declarativeRemainder expression
            output.declarativeRemainder)
    {input output : State} {expression : Expr}
    (result : conditional nested alternative input = .ok expression output) :
    DeclarativeGrammar.ConditionalOrdinaryParses nestedOrdinary
      alternativeOrdinary input.declarativeRemainder expression
        output.declarativeRemainder := by
  unfold conditional at result
  cases alternativeResult : alternative input with
  | invariant error => simp [alternativeResult] at result
  | reject failure rejected => simp [alternativeResult] at result
  | ok condition afterCondition =>
      simp only [alternativeResult] at result
      rcases conditionalTail_success_ordinary_sound_strong nested alternative
          nestedOrdinary alternativeOrdinary nestedSuccessSound
            alternativeSuccessSound (afterCondition.remainingCount + 1) []
              condition afterCondition expression output result with
        ⟨tailExpression, expressionEq, tailParsed⟩
      simp only [List.foldl_nil] at expressionEq
      subst expression
      exact ⟨condition, afterCondition.declarativeRemainder,
        alternativeSuccessSound alternativeResult, tailParsed⟩

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionConditionalOrdinaryRejectionSoundnessProperties
/-!
Exact executable rejection bridges for the generic Core conditional layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- Every executable conditional-tail rejection records the exact selected
suffix stage and all preceding ordinary subordinate outcomes. -/
theorem conditionalTail_reject_ordinary_sound
    (nested alternative : Parser Expr)
    (nestedOrdinary alternativeOrdinary :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop)
    (nestedRejects alternativeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (alternativeSuccessSound :
      ∀ {input output : State} {expression : Expr},
        alternative input = .ok expression output → alternativeOrdinary
          input.declarativeRemainder expression output.declarativeRemainder)
    (alternativeRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        alternative input = .reject failure rejected → alternativeRejects
          input.declarativeRemainder rejected.declarativeRemainder) :
    ∀ fuel headsRev condition input failure rejected,
      conditionalTail nested alternative fuel headsRev condition input =
          .reject failure rejected →
        DeclarativeGrammar.ConditionalTailRejects nestedOrdinary
          alternativeOrdinary nestedRejects alternativeRejects
            input.declarativeRemainder condition
              rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro headsRev condition input failure rejected result
      simp [conditionalTail] at result
  | succ fuel inductionHypothesis =>
      intro headsRev condition input failure rejected result
      unfold conditionalTail at result
      split at result
      next questionPresent =>
        cases questionResult : symbol .question .expression input with
        | invariant error => simp [questionResult] at result
        | reject questionFailure questionRejected =>
            rcases symbol_eq_ok_of_isSymbol_eq_true .question .expression
                questionPresent with ⟨question, parsed⟩
            rw [parsed] at questionResult
            contradiction
        | ok question afterQuestion =>
            simp only [questionResult] at result
            have questionParsed := symbol_success_exactTokenParses .question
              .expression questionResult
            cases thenResult : nested afterQuestion with
            | invariant error => simp [thenResult] at result
            | reject thenFailure thenRejected =>
                simp only [thenResult] at result
                cases result
                exact .thenRejected question.span questionParsed
                  (nestedRejectSound thenResult)
            | ok thenBranch afterThen =>
                simp only [thenResult] at result
                have thenParsed := nestedSuccessSound thenResult
                cases colonResult : symbol .colon .expression afterThen with
                | invariant error => simp [colonResult] at result
                | reject colonFailure colonRejected =>
                    have rejectedEq := symbol_reject_state_eq .colon .expression
                      colonResult
                    subst rejectedEq
                    simp only [colonResult] at result
                    cases result
                    exact .colonMissing question.span questionParsed thenParsed
                      (symbol_reject_tokenKindAbsentAt .colon .expression
                        colonResult)
                | ok colon afterColon =>
                    simp only [colonResult] at result
                    have colonParsed := symbol_success_exactTokenParses .colon
                      .expression colonResult
                    cases alternativeResult : alternative afterColon with
                    | invariant error => simp [alternativeResult] at result
                    | reject alternativeFailure alternativeRejected =>
                        simp only [alternativeResult] at result
                        cases result
                        exact .alternativeRejected question.span colon.span
                          questionParsed thenParsed colonParsed
                          (alternativeRejectSound alternativeResult)
                    | ok nextCondition afterAlternative =>
                        simp only [alternativeResult] at result
                        exact .laterRejected question.span colon.span
                          questionParsed thenParsed colonParsed
                          (alternativeSuccessSound alternativeResult)
                          (inductionHypothesis ({
                            condition
                            question := question.span
                            thenBranch
                            colon := colon.span
                          } :: headsRev) nextCondition afterAlternative failure
                            rejected result)
      next questionAbsent =>
        cases result

/-- Every executable complete conditional rejection is either its initial
alternative rejection or an exact rejection in the maximal conditional tail. -/
theorem conditional_reject_ordinary_sound
    (nested alternative : Parser Expr)
    (nestedOrdinary alternativeOrdinary :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop)
    (nestedRejects alternativeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (alternativeSuccessSound :
      ∀ {input output : State} {expression : Expr},
        alternative input = .ok expression output → alternativeOrdinary
          input.declarativeRemainder expression output.declarativeRemainder)
    (alternativeRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        alternative input = .reject failure rejected → alternativeRejects
          input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : conditional nested alternative input = .reject failure rejected) :
    DeclarativeGrammar.ConditionalRejects nestedOrdinary alternativeOrdinary
      nestedRejects alternativeRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold conditional at result
  cases alternativeResult : alternative input with
  | invariant error => simp [alternativeResult] at result
  | reject alternativeFailure alternativeRejected =>
      simp only [alternativeResult] at result
      cases result
      exact .conditionRejected (alternativeRejectSound alternativeResult)
  | ok condition afterCondition =>
      simp only [alternativeResult] at result
      exact .tailRejected (alternativeSuccessSound alternativeResult)
        (conditionalTail_reject_ordinary_sound nested alternative nestedOrdinary
          alternativeOrdinary nestedRejects alternativeRejects
            nestedSuccessSound nestedRejectSound alternativeSuccessSound
              alternativeRejectSound (afterCondition.remainingCount + 1) []
                condition afterCondition failure rejected result)

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionConditionalOrdinaryOutcomeSoundnessProperties
/-! Composed executable ordinary outcomes for Core conditional parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- Package complete conditional success and rejection over supplied recursive
and alternative outcomes. -/
theorem conditional_ordinaryOutcome_sound
    (nested alternative : Parser Expr)
    (nestedOrdinary alternativeOrdinary :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop)
    (nestedRejects alternativeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (alternativeSuccessSound :
      ∀ {input output : State} {expression : Expr},
        alternative input = .ok expression output → alternativeOrdinary
          input.declarativeRemainder expression output.declarativeRemainder)
    (alternativeRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        alternative input = .reject failure rejected → alternativeRejects
          input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {expression : Expr},
      conditional nested alternative input = .ok expression output →
        DeclarativeGrammar.ConditionalOrdinaryParses nestedOrdinary
          alternativeOrdinary input.declarativeRemainder expression
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      conditional nested alternative input = .reject failure rejected →
        DeclarativeGrammar.ConditionalRejects nestedOrdinary
          alternativeOrdinary nestedRejects alternativeRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨conditional_success_ordinary_sound nested alternative nestedOrdinary
      alternativeOrdinary nestedSuccessSound alternativeSuccessSound,
    conditional_reject_ordinary_sound nested alternative nestedOrdinary
      alternativeOrdinary nestedRejects alternativeRejects nestedSuccessSound
        nestedRejectSound alternativeSuccessSound alternativeRejectSound⟩

/-- Lift deterministic recursive and alternative outcomes through the
conditional layer. -/
theorem conditional_ordinaryOutcomeSpec
    {nestedOrdinary alternativeOrdinary :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop}
    {nestedRejects alternativeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects)
    (alternativeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      alternativeOrdinary alternativeRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ConditionalOrdinaryParses nestedOrdinary
        alternativeOrdinary)
      (DeclarativeGrammar.ConditionalRejects nestedOrdinary alternativeOrdinary
        nestedRejects alternativeRejects) :=
  DeclarativeGrammar.conditionalDeterministicOutcomeSpec nestedOutcomes
    alternativeOutcomes

end Solcore.Syntax.Parser.ExpressionInternals
end
