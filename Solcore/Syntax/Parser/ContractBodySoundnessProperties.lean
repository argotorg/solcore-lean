import Solcore.Syntax.Parser.ContractBodyProperties
import Solcore.Syntax.Parser.ContractBodyDiagnosticReflectionProperties
import Solcore.Syntax.Parser.ContractMemberSoundnessProperties

/-! Parametric diagnostic-free soundness for fuel-bounded contract bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

private theorem bind_ok_components {alpha beta : Type} {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

private theorem closeContractBody_success_sound_and_reflects
    (opening : Token) (membersRev : List ContractMember)
    {input next : State} {body : ContractBody}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : closeContractBody opening membersRev input = .ok body next) :
    ∃ closingSpan,
      body = {
        span := SourceSpan.cover opening.span closingSpan
        members := membersRev.reverse
      } ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan next.declarativeRemainder ∧
      input.diagnosticsRev = [] := by
  unfold closeContractBody at result
  rcases bind_ok_components result with
    ⟨closing, afterClosing, closingResult, finished⟩
  have afterClosingFree : afterClosing.diagnosticsRev = [] := by
    cases finished
    exact diagnosticFree
  have inputFree : input.diagnosticsRev = [] :=
    symbol_reflectsDiagnosticFreeOnSuccess .rightBrace .topItem input closing
      afterClosing closingResult afterClosingFree
  cases finished
  exact ⟨closing.span, rfl,
    symbol_success_exactTokenParses .rightBrace .topItem closingResult,
    inputFree⟩

private theorem contractMembers_success_sound_strong
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      DeclarativeGrammar.Remainder → Block →
        DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (allowBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      allowBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (requiredBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      requiredBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (opening : Token) :
    ∀ fuel membersRev input body next,
      next.diagnosticsRev = [] →
      contractMembers opening fuel membersRev input = .ok body next →
      ∃ members closingSpan,
        body = {
          span := SourceSpan.cover opening.span closingSpan
          members := membersRev.reverse ++ members
        } ∧
        DeclarativeGrammar.ContractMemberTailParses expressionParses
          allowBodyParses requiredBodyParses input.declarativeRemainder
            members closingSpan next.declarativeRemainder ∧
        input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro membersRev input body next diagnosticFree result
      simp [contractMembers] at result
  | succ fuel inductionHypothesis =>
      intro membersRev input body next diagnosticFree result
      unfold contractMembers at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeContractBody_success_sound_and_reflects opening membersRev
              diagnosticFree result with
            ⟨closingSpan, bodyEq, closingGrammar, inputFree⟩
          exact ⟨[], closingSpan, by simpa using bodyEq,
            .close closingSpan closingGrammar, inputFree⟩
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
                    rcases inductionHypothesis (member :: membersRev)
                        afterMember body next diagnosticFree result with
                      ⟨members, closingSpan, bodyEq, tailGrammar,
                        afterMemberFree⟩
                    have memberGrammar :=
                      contractMemberWithAttribute_success_sound expressionParses
                        allowBodyParses requiredBodyParses expressionReflects
                        expressionSound allowBodyReflects allowBodySound
                        requiredBodyReflects requiredBodySound afterMemberFree
                        memberResult
                    have inputFree :=
                      contractMemberWithAttribute_reflectsDiagnosticFreeOnSuccess
                        expressionReflects allowBodyReflects requiredBodyReflects
                          input member afterMember memberResult afterMemberFree
                    refine ⟨member :: members, closingSpan, ?_,
                      .next
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingPresent)
                        memberGrammar progress tailGrammar,
                      inputFree⟩
                    simpa [List.reverse_cons, List.append_assoc] using bodyEq
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
                        rcases inductionHypothesis (member :: membersRev)
                            afterRecovery body next diagnosticFree result with
                          ⟨members, closingSpan, bodyEq, tailGrammar,
                            afterRecoveryFree⟩
                        exact (recoverContractMember_success_hasDiagnostic
                          recoveryResult afterRecoveryFree).elim

/-! Every diagnostic-free contract body has exact braces, member order,
branch priority, and strict member progress under the supplied leaf grammars. -/
theorem contractBody_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      DeclarativeGrammar.Remainder → Block →
        DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (allowBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      allowBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (requiredBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      requiredBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {body : ContractBody}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : contractBody input = .ok body next) :
    DeclarativeGrammar.ContractBodyParses expressionParses allowBodyParses
      requiredBodyParses input.declarativeRemainder body.span body.members
        next.declarativeRemainder := by
  unfold contractBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases contractMembers_success_sound_strong expressionParses
          allowBodyParses requiredBodyParses expressionReflects expressionSound
          allowBodyReflects allowBodySound requiredBodyReflects requiredBodySound
          opening (afterOpening.remainingCount + 1) [] afterOpening body next
          diagnosticFree result with
        ⟨members, closingSpan, bodyEq, tailGrammar, afterOpeningFree⟩
      rw [bodyEq]
      simpa using DeclarativeGrammar.ContractBodyParses.parsed opening.span
        closingSpan
        (symbol_success_exactTokenParses .leftBrace .topItem openingResult)
        tailGrammar

/-- Contract-body grammar soundness composes with canonical source validity. -/
theorem contractBody_success_sound_and_validFor
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      DeclarativeGrammar.Remainder → Block →
        DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (allowBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      allowBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (requiredBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      requiredBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {body : ContractBody} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : contractBody input = .ok body next) :
    DeclarativeGrammar.ContractBodyParses expressionParses allowBodyParses
        requiredBodyParses input.declarativeRemainder body.span body.members
          next.declarativeRemainder ∧
      ContractBody.ValidFor input.file body := by
  refine ⟨contractBody_success_sound expressionParses allowBodyParses
    requiredBodyParses expressionReflects expressionSound allowBodyReflects
    allowBodySound requiredBodyReflects requiredBodySound diagnosticFree result,
    ?_⟩
  have valid := contractBody_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.ContractInternals
