import Solcore.Syntax.DeclarativeCoreExpressionLayerGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.ExpressionProperties

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
