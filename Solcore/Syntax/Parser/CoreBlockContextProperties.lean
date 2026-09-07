import Solcore.Syntax.Parser.StatementDiagnosticTraceContracts

/-! Successful raw Core blocks preserve source and the complete token/byte
window under the corresponding inner statement frame law, for arbitrary events. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem coreBlockItems_success_context_eq
    {statement : Parser Statement} (contextFrame : StatementSuccessContext statement)
    (opening : Token) (policy : TailExpressionPolicy) :
    ∀ fuel bodyRev input body output,
      coreBlockItems statement opening policy fuel bodyRev input = .ok body output →
        output.file = input.file ∧ output.window = input.window := by
  intro fuel
  induction fuel with
  | zero => intro bodyRev input body output result; simp [coreBlockItems] at result
  | succ fuel ih =>
      intro bodyRev input body output result
      unfold coreBlockItems at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          exact closeCoreBlock_success_context_eq opening policy bodyRev result
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .statement input <;> simp [closingResult] at result
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              cases statementResult : statement input with
              | invariant error => simp [statementResult] at result
              | reject failure rejected => simp [statementResult] at result
              | ok value next =>
                  simp only [statementResult] at result
                  by_cases progress : next.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    have tail := ih (value :: bodyRev) next body output result
                    have head := contextFrame statementResult
                    exact ⟨tail.1.trans head.1, tail.2.trans head.2⟩
                  · simp only [progress, if_false] at result
                    contradiction

theorem coreBlock_success_context_eq
    {statement : Parser Statement} (contextFrame : StatementSuccessContext statement)
    (policy : TailExpressionPolicy) {input output : State} {body : Block}
    (result : coreBlock statement policy input = .ok body output) :
    output.file = input.file ∧ output.window = input.window := by
  unfold coreBlock at result
  cases openingResult : symbol .leftBrace .statement input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have frame := coreBlockItems_success_context_eq contextFrame opening policy
        (afterOpening.remainingCount + 1) [] afterOpening body output result
      have shape := (symbol_ok_tokenAt .leftBrace .statement openingResult).2
      simpa only [shape] using frame

end Solcore.Syntax.Parser
