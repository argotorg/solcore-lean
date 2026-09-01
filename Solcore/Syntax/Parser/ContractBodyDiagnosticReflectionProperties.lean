import Solcore.Syntax.Parser.ContractMemberSoundnessProperties
import Solcore.Syntax.Parser.ContractRecoveryDiagnosticProperties

/-! Diagnostic-freedom reflection through fuel-bounded contract bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

private theorem closeContractBody_reflectsDiagnosticFreeOnSuccess
    (opening : Token) (membersRev : List ContractMember) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (closeContractBody opening membersRev) := by
  unfold closeContractBody
  exact Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .rightBrace .topItem)
    (fun _ => Parser.pure_reflectsDiagnosticFreeOnSuccess _)

private theorem contractMembers_reflectsDiagnosticFreeOnSuccess
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require))) (opening : Token) :
    ∀ fuel membersRev input body next,
      contractMembers opening fuel membersRev input = .ok body next →
      next.diagnosticsRev = [] → input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro membersRev input body next result diagnosticFree
      simp [contractMembers] at result
  | succ fuel inductionHypothesis =>
      intro membersRev input body next result diagnosticFree
      unfold contractMembers at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          exact closeContractBody_reflectsDiagnosticFreeOnSuccess opening
            membersRev input body next result diagnosticFree
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .topItem input <;>
                simp [closingResult] at result
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              cases memberResult : contractMemberWithAttribute input with
              | invariant error => simp [memberResult] at result
              | ok member afterMember =>
                  simp only [memberResult] at result
                  by_cases progress : afterMember.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    have afterMemberFree := inductionHypothesis
                      (member :: membersRev) afterMember body next result
                        diagnosticFree
                    exact contractMemberWithAttribute_reflectsDiagnosticFreeOnSuccess
                      expressionReflects allowBodyReflects requiredBodyReflects
                        input member afterMember memberResult afterMemberFree
                  · simp only [progress, if_false] at result
                    contradiction
              | reject failure failedState =>
                  simp only [memberResult] at result
                  let rewound : State := {
                    failedState with cursor := input.cursor
                  }
                  change (if atContractRecoveryBoundary input then
                      .reject failure rewound
                    else match recoverContractMember rewound with
                      | .ok member afterRecovery =>
                          contractMembers opening fuel
                            (member :: membersRev) afterRecovery
                      | .reject recoveryFailure rejected =>
                          .reject recoveryFailure rejected
                      | .invariant error => .invariant error) =
                    .ok body next at result
                  split at result
                  · contradiction
                  · cases recoveryResult : recoverContractMember rewound with
                    | invariant error => simp [recoveryResult] at result
                    | reject recoveryFailure rejected =>
                        simp [recoveryResult] at result
                    | ok member afterRecovery =>
                        simp only [recoveryResult] at result
                        have afterRecoveryFree := inductionHypothesis
                          (member :: membersRev) afterRecovery body next result
                            diagnosticFree
                        exact (recoverContractMember_success_hasDiagnostic
                          recoveryResult afterRecoveryFree).elim

/-- Contract-body parsing cannot erase an incoming diagnostic. -/
theorem contractBody_reflectsDiagnosticFreeOnSuccess
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require))) :
    Parser.ReflectsDiagnosticFreeOnSuccess contractBody := by
  intro input body next result diagnosticFree
  unfold contractBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have afterOpeningFree := contractMembers_reflectsDiagnosticFreeOnSuccess
        expressionReflects allowBodyReflects requiredBodyReflects opening
          (afterOpening.remainingCount + 1) [] afterOpening body next result
            diagnosticFree
      exact symbol_reflectsDiagnosticFreeOnSuccess .leftBrace .topItem input
        opening afterOpening openingResult afterOpeningFree

end Solcore.Syntax.Parser.ContractInternals
