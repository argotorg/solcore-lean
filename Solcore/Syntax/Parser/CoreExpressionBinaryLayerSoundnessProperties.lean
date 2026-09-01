import Solcore.Syntax.Parser.CoreExpressionBinaryOperatorSoundnessProperties

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
          let afterOperator := { input with cursor := input.cursor + 1 }
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
          let afterOperator := { input with cursor := input.cursor + 1 }
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
            cursor := afterLeft.cursor + 1 }
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
            cursor := afterLeft.cursor + 1 }
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
