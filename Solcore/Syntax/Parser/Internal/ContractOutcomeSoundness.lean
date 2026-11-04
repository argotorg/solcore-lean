import Solcore.Syntax.Internal.DeriveOutcomes
import Solcore.Syntax.Parser.Internal.ContractProofs
import Solcore.Syntax.Parser.Internal.DeclarationTotality
import Solcore.Syntax.Parser.Internal.ContractBodySoundness
import Solcore.Syntax.Internal.ContractBodyOutcomes
import Solcore.Syntax.Grammar.Declarations
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.SignatureSoundness
import Solcore.Syntax.Parser.Internal.YulExpressionSoundness
import Solcore.Syntax.Internal.DeclarationExactness
import Solcore.Syntax.Parser.Internal.TermSoundness
import Solcore.Syntax.Parser.Internal.ImplProofs

/-!
Soundness of the parsers of whole contract declarations: each success and each rejection
has its declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.ContractMemberRecoveryOrdinaryOutcomeSoundnessProperties
/-! Exact executable ordinary outcomes for contract-member recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

private theorem advance?_state_shape {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    input.peek? = some token ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      exact ⟨rfl, rfl⟩

/-- Every successful auxiliary recovery scan records its exact consumed token
sequence, stopping boundary, recovered span, AST, and final remainder. -/
theorem recoverContractMemberAux_success_ordinaryOutcome_sound
    (first : SourceSpan) :
    ∀ fuel last input member output,
      recoverContractMemberAux first last fuel input = .ok member output →
      DeclarativeGrammar.ContractMemberRecoveryScanParses first last
        input.declarativeRemainder member output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input member output result
      simp [recoverContractMemberAux] at result
  | succ fuel inductionHypothesis =>
      intro last input member output result
      unfold recoverContractMemberAux at result
      by_cases guard :
          (input.atEnd || atContractRecoveryBoundary input) = true
      · simp only [guard, if_true] at result
        unfold finishRecoveredMember at result
        cases result
        simpa [State.emit, State.declarativeRemainder,
          DeclarativeGrammar.recoveredContractMemberValue] using
          (DeclarativeGrammar.ContractMemberRecoveryScanParses.stop
            (first := first) (last := last)
            (contractMemberRecoveryStops_of_guard_eq_true input guard))
      · have guardFalse :
            (input.atEnd || atContractRecoveryBoundary input) = false :=
          Bool.eq_false_iff.mpr guard
        simp only [guardFalse, Bool.false_eq_true, if_false] at result
        cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredMember at result
            cases result
            simpa [State.emit, State.declarativeRemainder,
              DeclarativeGrammar.recoveredContractMemberValue] using
              (DeclarativeGrammar.ContractMemberRecoveryScanParses.stop
                (first := first) (last := last)
                (contractMemberRecoveryStops_of_advance?_eq_none input
                  guardFalse advanced))
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            rcases advance?_state_shape advanced with ⟨found, nextEq⟩
            have tail := inductionHypothesis token.span next member output result
            rw [nextEq] at tail
            exact .next
              (no_contractMemberRecoveryStops_of_nonBoundary_token
                guardFalse found)
              (tokenAt_of_peek?_eq_some found) tail

/-- Every executable recovery success consumes its mandatory first token and
then follows the exact boundary-preserving scan. -/
theorem recoverContractMember_success_ordinaryOutcome_sound
    {input output : State} {member : ContractMember}
    (result : recoverContractMember input = .ok member output) :
    DeclarativeGrammar.ContractMemberRecoveryParses
      input.declarativeRemainder member output.declarativeRemainder := by
  unfold recoverContractMember at result
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at result
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases advance?_state_shape advanced with ⟨found, nextEq⟩
      have scan := recoverContractMemberAux_success_ordinaryOutcome_sound
        token.span (next.remainingCount + 1) token.span next member output result
      rw [nextEq] at scan
      exact .recovered (tokenAt_of_peek?_eq_some found) scan

/-- Every executable recovery rejection exactly records an unavailable
mandatory first token and retains the complete declarative remainder. -/
theorem recoverContractMember_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : recoverContractMember input = .reject failure rejected) :
    DeclarativeGrammar.ContractMemberRecoveryRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold recoverContractMember at result
  cases advanced : input.advance? with
  | none =>
      simp only [advanced] at result
      unfold rejectAt at result
      cases result
      by_cases atEnd : input.window.endIndex ≤ input.cursor
      · exact .windowEnd atEnd
      · have inside : input.cursor < input.window.endIndex := by omega
        apply DeclarativeGrammar.ContractMemberRecoveryRejects.missingToken
          inside
        unfold State.advance? State.peek? at advanced
        simpa [State.declarativeRemainder, inside] using advanced
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases recoverContractMemberAux_production_ok token.span token.span next
          with ⟨recovered, output, recoveredResult⟩
      rw [recoveredResult] at result
      contradiction

/-- Package standalone contract-member recovery success and rejection. -/
theorem recoverContractMember_ordinaryOutcome_sound :
    (∀ {input output : State} {member : ContractMember},
      recoverContractMember input = .ok member output →
        DeclarativeGrammar.ContractMemberRecoveryParses
          input.declarativeRemainder member output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      recoverContractMember input = .reject failure rejected →
        DeclarativeGrammar.ContractMemberRecoveryRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨recoverContractMember_success_ordinaryOutcome_sound,
    recoverContractMember_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic standalone recovery outcomes. -/
theorem recoverContractMember_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberRecoveryParses
      DeclarativeGrammar.ContractMemberRecoveryRejects :=
  DeclarativeGrammar.contractMemberRecoveryDeterministicOutcomeSpec

/-- Re-export exact contract-member recovery functionality at the executable
boundary. -/
theorem recoverContractMember_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberRecoveryParses
      DeclarativeGrammar.ContractMemberRecoveryRejects :=
  DeclarativeGrammar.contractMemberRecoveryExactOutcomeSpec

/-- Two successful recovery reflections have the same member AST and final
declarative remainder. -/
theorem recoverContractMember_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : ContractMember}
    (leftResult : recoverContractMember input = .ok left leftOutput)
    (rightResult : recoverContractMember input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ContractMemberRecoveryParses.result_unique
    (recoverContractMember_success_ordinaryOutcome_sound leftResult)
    (recoverContractMember_success_ordinaryOutcome_sound rightResult)

/-- Two recovery rejections have the same exact declarative endpoint. -/
theorem recoverContractMember_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : recoverContractMember input =
      .reject leftFailure leftOutput)
    (rightResult : recoverContractMember input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ContractMemberRecoveryRejects.output_unique
    (recoverContractMember_reject_ordinaryOutcome_sound leftResult)
    (recoverContractMember_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractBodyTailOrdinarySuccessSoundnessProperties
/-! Broad ordinary-success soundness for contract-body member tails. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Every successful fuel-bounded member loop exposes its exact closing brace,
new members in source order, and the corresponding broad ordinary tail. -/
theorem contractMembers_success_ordinaryOutcome_sound_strong
    (opening : Token) :
    ∀ fuel membersRev input body output,
      contractMembers opening fuel membersRev input = .ok body output →
      ∃ members closingSpan,
        body = {
          span := SourceSpan.cover opening.span closingSpan
          members := membersRev.reverse ++ members
        } ∧
        DeclarativeGrammar.ContractMemberTailOrdinaryParses
          input.declarativeRemainder members closingSpan
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro membersRev input body output result
      simp [contractMembers] at result
  | succ fuel inductionHypothesis =>
      intro membersRev input body output result
      unfold contractMembers at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeContractBody_success_exact opening membersRev result with
            ⟨closingSpan, bodyEq, closingParsed⟩
          exact ⟨[], closingSpan, by simpa using bodyEq,
            .close closingSpan closingParsed⟩
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .topItem input <;>
                simp [closingResult] at result
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              have closingAbsent :=
                symbolAbsentAt_of_isSymbol_eq_false .rightBrace closingPresent
              have inside := cursor_lt_endIndex_of_atEnd_eq_false ended
              cases memberResult : contractMemberWithAttribute input with
              | invariant error => simp [memberResult] at result
              | ok member afterMember =>
                  simp only [memberResult] at result
                  by_cases progress : afterMember.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases inductionHypothesis (member :: membersRev)
                        afterMember body output result with
                      ⟨members, closingSpan, bodyEq, tailParsed⟩
                    refine ⟨member :: members, closingSpan, ?_,
                      .direct closingAbsent inside
                        (contractMemberWithAttribute_success_ordinaryOutcome_sound
                          memberResult)
                        progress tailParsed⟩
                    simpa [List.reverse_cons, List.append_assoc] using bodyEq
                  · simp only [progress, if_false] at result
                    contradiction
              | reject failure failedState =>
                  simp only [memberResult] at result
                  have memberRejected :=
                    contractMemberRejectsWithPreservedWindow_of_result
                      memberResult
                  have resultShape :=
                    contractMemberWithAttribute_canonical_contract
                      |>.preservesTokenWindow input
                  rw [memberResult] at resultShape
                  have shape : failedState.tokens = input.tokens ∧
                      failedState.window = input.window := by
                    simpa only [Reply.PreservesTokenWindow] using resultShape
                  let rewound : State := {
                    failedState with cursor := input.cursor
                  }
                  have rewoundEq : rewound.declarativeRemainder =
                      input.declarativeRemainder := by
                    dsimp only [rewound]
                    exact rewoundContractMember_declarativeRemainder_eq
                      input failedState shape
                  change (if atContractRecoveryBoundary input then
                      .reject failure rewound
                    else match recoverContractMember rewound with
                      | .ok member afterRecovery =>
                          contractMembers opening fuel
                            (member :: membersRev) afterRecovery
                      | .reject recoveryFailure rejected =>
                          .reject recoveryFailure rejected
                      | .invariant error => .invariant error) =
                    .ok body output at result
                  cases boundary : atContractRecoveryBoundary input with
                  | true => simp [boundary] at result
                  | false =>
                      simp only [boundary, Bool.false_eq_true, if_false]
                        at result
                      cases recoveryResult : recoverContractMember rewound with
                      | invariant error => simp [recoveryResult] at result
                      | reject recoveryFailure rejected =>
                          simp [recoveryResult] at result
                      | ok member afterRecovery =>
                          simp only [recoveryResult] at result
                          rcases inductionHypothesis (member :: membersRev)
                              afterRecovery body output result with
                            ⟨members, closingSpan, bodyEq, tailParsed⟩
                          have recoveryParsed :=
                            recoverContractMember_success_ordinaryOutcome_sound
                              recoveryResult
                          rw [rewoundEq] at recoveryParsed
                          refine ⟨member :: members, closingSpan, ?_,
                            .recovered closingAbsent inside memberRejected
                              (no_contractMemberRecoveryBoundaryStartsAt_of_guard_eq_false
                                boundary)
                              recoveryParsed tailParsed⟩
                          simpa [List.reverse_cons, List.append_assoc]
                            using bodyEq

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractBodyTailOrdinaryRejectionSoundnessProperties
/-! Broad ordinary-rejection soundness for contract-body member tails. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Every rejecting fuel-bounded member loop records the exact first rejection
of its prioritized close, member, rewind, recovery, and recursive branches. -/
theorem contractMembers_reject_ordinaryOutcome_sound
    (opening : Token) :
    ∀ fuel membersRev input failure rejected,
      contractMembers opening fuel membersRev input =
        .reject failure rejected →
      DeclarativeGrammar.ContractMemberTailRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro membersRev input failure rejected result
      simp [contractMembers] at result
  | succ fuel inductionHypothesis =>
      intro membersRev input failure rejected result
      unfold contractMembers at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeContractBody_success_of_rightBrace_guard opening
              membersRev closingPresent with
            ⟨body, output, successful⟩
          rw [successful] at result
          contradiction
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          have closingAbsent :=
            symbolAbsentAt_of_isSymbol_eq_false .rightBrace closingPresent
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              have atEnd : input.window.endIndex ≤ input.cursor := by
                simpa [State.atEnd] using ended
              cases closingResult : symbol .rightBrace .topItem input with
              | invariant error => simp [closingResult] at result
              | ok closing afterClosing => simp [closingResult] at result
              | reject closingFailure closingRejected =>
                  have rejectedEq := symbol_reject_state_eq .rightBrace
                    .topItem closingResult
                  subst closingRejected
                  simp only [closingResult] at result
                  cases result
                  exact .windowEnd closingAbsent atEnd
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              have inside := cursor_lt_endIndex_of_atEnd_eq_false ended
              cases memberResult : contractMemberWithAttribute input with
              | invariant error => simp [memberResult] at result
              | ok member afterMember =>
                  simp only [memberResult] at result
                  by_cases progress : afterMember.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    exact .laterDirect closingAbsent inside
                      (contractMemberWithAttribute_success_ordinaryOutcome_sound
                        memberResult)
                      progress
                      (inductionHypothesis (member :: membersRev) afterMember
                        failure rejected result)
                  · simp only [progress, if_false] at result
                    contradiction
              | reject memberFailure failedState =>
                  simp only [memberResult] at result
                  have memberRejected :=
                    contractMemberRejectsWithPreservedWindow_of_result
                      memberResult
                  have resultShape :=
                    contractMemberWithAttribute_canonical_contract
                      |>.preservesTokenWindow input
                  rw [memberResult] at resultShape
                  have shape : failedState.tokens = input.tokens ∧
                      failedState.window = input.window := by
                    simpa only [Reply.PreservesTokenWindow] using resultShape
                  let rewound : State := {
                    failedState with cursor := input.cursor
                  }
                  have rewoundEq : rewound.declarativeRemainder =
                      input.declarativeRemainder := by
                    dsimp only [rewound]
                    exact rewoundContractMember_declarativeRemainder_eq
                      input failedState shape
                  change (if atContractRecoveryBoundary input then
                      .reject memberFailure rewound
                    else match recoverContractMember rewound with
                      | .ok member afterRecovery =>
                          contractMembers opening fuel
                            (member :: membersRev) afterRecovery
                      | .reject recoveryFailure recoveryRejected =>
                          .reject recoveryFailure recoveryRejected
                      | .invariant error => .invariant error) =
                    .reject failure rejected at result
                  cases boundary : atContractRecoveryBoundary input with
                  | true =>
                      simp only [boundary, if_true] at result
                      have rejectedEq : rewound = rejected := by
                        injection result
                      rw [← rejectedEq, rewoundEq]
                      exact .memberAtBoundary closingAbsent inside
                        memberRejected
                        (contractMemberRecoveryBoundaryStartsAt_of_guard_eq_true
                          boundary)
                  | false =>
                      simp only [boundary, Bool.false_eq_true, if_false]
                        at result
                      have boundaryAbsent :=
                        no_contractMemberRecoveryBoundaryStartsAt_of_guard_eq_false
                          boundary
                      cases recoveryResult : recoverContractMember rewound with
                      | invariant error => simp [recoveryResult] at result
                      | reject recoveryFailure recoveryRejected =>
                          simp only [recoveryResult] at result
                          cases result
                          have recoveryGrammar :=
                            recoverContractMember_reject_ordinaryOutcome_sound
                              recoveryResult
                          rw [rewoundEq] at recoveryGrammar
                          exact .recoveryRejected closingAbsent inside
                            memberRejected boundaryAbsent recoveryGrammar
                      | ok member afterRecovery =>
                          simp only [recoveryResult] at result
                          have recoveryGrammar :=
                            recoverContractMember_success_ordinaryOutcome_sound
                              recoveryResult
                          rw [rewoundEq] at recoveryGrammar
                          exact .laterRecovered closingAbsent inside
                            memberRejected boundaryAbsent recoveryGrammar
                            (inductionHypothesis (member :: membersRev)
                              afterRecovery failure rejected result)

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractBodyOrdinaryOutcomeSoundnessProperties
/-! Complete broad executable outcomes for recovery-aware contract bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Every successful public contract-body parse has exact braces, covered
span, source-order direct/recovered members, and final remainder. -/
theorem contractBody_success_ordinaryOutcome_sound
    {input output : State} {body : ContractBody}
    (result : contractBody input = .ok body output) :
    DeclarativeGrammar.ContractBodyOrdinaryParses input.declarativeRemainder
      body.span body.members output.declarativeRemainder := by
  unfold contractBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases contractMembers_success_ordinaryOutcome_sound_strong opening
          (afterOpening.remainingCount + 1) [] afterOpening body output result
          with ⟨members, closingSpan, bodyEq, tailParsed⟩
      rw [bodyEq]
      simpa using
        (DeclarativeGrammar.ContractBodyOrdinaryParses.parsed opening.span
          closingSpan
          (symbol_success_exactTokenParses .leftBrace .topItem openingResult)
          tailParsed)

/-- Every public contract-body rejection records an opening-brace failure or
the exact first rejection of the recovery-aware member loop. -/
theorem contractBody_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : contractBody input = .reject failure rejected) :
    DeclarativeGrammar.ContractBodyRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold contractBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingRejected =>
      simp only [openingResult] at result
      have rejectedEq : openingRejected = rejected := by injection result
      rw [← rejectedEq,
        symbol_reject_state_eq .leftBrace .topItem openingResult]
      exact .openingMissing
        (symbol_reject_tokenKindAbsentAt .leftBrace .topItem openingResult)
  | ok opening afterOpening =>
      simp only [openingResult] at result
      exact .tailRejected opening.span
        (symbol_success_exactTokenParses .leftBrace .topItem openingResult)
        (contractMembers_reject_ordinaryOutcome_sound opening
          (afterOpening.remainingCount + 1) [] afterOpening failure rejected
          result)

/-- Package unconditional public contract-body success and exact rejection. -/
theorem contractBody_ordinaryOutcome_sound :
    (∀ {input output : State} {body : ContractBody},
      contractBody input = .ok body output →
        DeclarativeGrammar.ContractBodyOrdinaryParses
          input.declarativeRemainder body.span body.members
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      contractBody input = .reject failure rejected →
        DeclarativeGrammar.ContractBodyRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨contractBody_success_ordinaryOutcome_sound,
    contractBody_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad contract-body outcomes. -/
theorem contractBody_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ContractBodyRejects :=
  DeclarativeGrammar.contractBodyDeterministicOutcomeSpec

/-- Exact derive-aware member outcomes lift through contract-body recovery. -/
theorem contractBody_exactOutcomeSpec_of_member
    (memberOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberOrdinaryParses
      DeclarativeGrammar.ContractMemberRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ContractBodyRejects :=
  DeclarativeGrammar.contractBodyExactOutcomeSpecOfMember memberOutcomes

/-- Exact attribute-free member outcomes lift through derive attachment and
contract-body recovery. -/
theorem contractBody_exactOutcomeSpec_of_core
    (coreOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ContractBodyRejects :=
  DeclarativeGrammar.contractBodyExactOutcomeSpecOfCore coreOutcomes

/-- Fixed-fuel Core expression and statement exactness alone supplies exact
recovery-aware contract-body outcomes. -/
theorem contractBody_exactOutcomeSpec_of_coreTermFuel
    (expressionOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreExpressionOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ContractBodyRejects :=
  DeclarativeGrammar.contractBodyExactOutcomeSpecOfCoreTermFuel
    expressionOutcomes statementOutcomes

/-- Under exact member outcomes, two executable bodies have the same value
and declarative remainder. -/
theorem contractBody_success_result_unique_of_member
    (memberOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberOrdinaryParses
      DeclarativeGrammar.ContractMemberRejects)
    {input leftOutput rightOutput : State}
    {left right : ContractBody}
    (leftResult : contractBody input = .ok left leftOutput)
    (rightResult : contractBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder := by
  rcases (contractBody_exactOutcomeSpec_of_member memberOutcomes)
      |>.successResultUnique
        (show DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
          input.declarativeRemainder (left.span, left.members)
            leftOutput.declarativeRemainder from
          contractBody_success_ordinaryOutcome_sound leftResult)
        (show DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
          input.declarativeRemainder (right.span, right.members)
            rightOutput.declarativeRemainder from
          contractBody_success_ordinaryOutcome_sound rightResult) with
    ⟨bodyEq, outputEq⟩
  constructor
  · cases left
    cases right
    simp_all
  · exact outputEq

/-- Under exact member outcomes, two body rejections have one declarative
endpoint. -/
theorem contractBody_reject_output_unique_of_member
    (memberOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberOrdinaryParses
      DeclarativeGrammar.ContractMemberRejects)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : contractBody input = .reject leftFailure leftOutput)
    (rightResult : contractBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (contractBody_exactOutcomeSpec_of_member memberOutcomes).rejectOutputUnique
    (contractBody_reject_ordinaryOutcome_sound leftResult)
    (contractBody_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractDeclarationOrdinaryRejectionSoundnessProperties
/-! Exact broad ordinary rejection for complete contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable contract-declaration rejection occurs at the first of
its marker, name, optional generic parameters, or recovery-aware body. -/
theorem contractDecl_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : contractDecl input = .reject failure rejected) :
    DeclarativeGrammar.ContractDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold contractDecl at result
  cases markerResult : keyword .contractKw .topItem input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .contractKw .topItem
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .contractKw .topItem markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .contractKw
        .topItem markerResult
      cases nameResult : identifier .topItem afterMarker with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          exact .nameRejected marker.span markerParsed
            (identifier_reject_sound .topItem nameResult)
      | ok name afterName =>
          simp only [nameResult] at result
          have nameParsed := identifier_success_sound .topItem nameResult
          cases genericsResult : optionalGenericParameters afterName with
          | invariant error => simp [genericsResult] at result
          | reject genericsFailure genericsRejected =>
              simp only [genericsResult] at result
              cases result
              exact .genericsRejected marker.span markerParsed nameParsed
                (optionalGenericParameters_ordinaryOutcome_sound.2
                  genericsResult)
          | ok genericParameters afterGenerics =>
              simp only [genericsResult] at result
              have genericsParsed :=
                optionalGenericParameters_ordinaryOutcome_sound.1
                  genericsResult
              cases bodyResult : ContractInternals.contractBody afterGenerics with
              | invariant error => simp [bodyResult] at result
              | reject bodyFailure bodyRejected =>
                  simp only [bodyResult] at result
                  cases result
                  exact .bodyRejected marker.span markerParsed nameParsed
                    genericsParsed
                    (ContractInternals.contractBody_reject_ordinaryOutcome_sound
                      bodyResult)
              | ok body output => simp [bodyResult, pure] at result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractDeclarationOrdinarySuccessSoundnessProperties
/-! Broad ordinary-success soundness for complete contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Every executable contract declaration success records its exact marker,
name, optional generic parameters, broad recovery-aware body, constructed AST,
covered span, and final remainder without a diagnostic-free premise. -/
theorem contractDecl_success_ordinaryOutcome_sound
    {input output : State} {declaration : ContractDecl}
    (result : contractDecl input = .ok declaration output) :
    DeclarativeGrammar.ContractDeclOrdinaryParses input.declarativeRemainder
      declaration output.declarativeRemainder := by
  unfold contractDecl at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases bind_ok_components rest with
    ⟨genericParameters, afterGenerics, genericsResult, rest⟩
  rcases bind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span
    (keyword_success_exactTokenParses .contractKw .topItem markerResult)
    (identifier_success_sound .topItem nameResult)
    (optionalGenericParameters_ordinaryOutcome_sound.1 genericsResult)
    (ContractInternals.contractBody_success_ordinaryOutcome_sound bodyResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractDeclarationOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package executable contract-declaration success and exact four-stage
rejection. -/
theorem contractDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : ContractDecl},
      contractDecl input = .ok declaration output →
        DeclarativeGrammar.ContractDeclOrdinaryParses
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      contractDecl input = .reject failure rejected →
        DeclarativeGrammar.ContractDeclRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨contractDecl_success_ordinaryOutcome_sound,
    contractDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad contract-declaration
outcomes. -/
theorem contractDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ContractDeclOrdinaryParses
      DeclarativeGrammar.ContractDeclRejects :=
  DeclarativeGrammar.contractDeclDeterministicOutcomeSpec

/-- An exact contract body lifts to exact complete declaration outcomes. -/
theorem contractDecl_exactOutcomeSpec_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ContractBodyRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractDeclOrdinaryParses
      DeclarativeGrammar.ContractDeclRejects :=
  DeclarativeGrammar.contractDeclExactOutcomeSpecOfBody bodyOutcomes

/-- Exact attribute-free member outcomes lift through the complete contract. -/
theorem contractDecl_exactOutcomeSpec_of_core
    (coreOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractDeclOrdinaryParses
      DeclarativeGrammar.ContractDeclRejects :=
  DeclarativeGrammar.contractDeclExactOutcomeSpecOfCore coreOutcomes

/-- Fixed-fuel Core expression and statement exactness alone supplies exact
complete contract-declaration outcomes. -/
theorem contractDecl_exactOutcomeSpec_of_coreTermFuel
    (expressionOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreExpressionOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractDeclOrdinaryParses
      DeclarativeGrammar.ContractDeclRejects :=
  DeclarativeGrammar.contractDeclExactOutcomeSpecOfCoreTermFuel
    expressionOutcomes statementOutcomes

/-- Under an exact body contract, two executable declarations have the same
AST and declarative remainder. -/
theorem contractDecl_success_result_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ContractBodyRejects)
    {input leftOutput rightOutput : State} {left right : ContractDecl}
    (leftResult : contractDecl input = .ok left leftOutput)
    (rightResult : contractDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (contractDecl_exactOutcomeSpec_of_body bodyOutcomes).successResultUnique
    (contractDecl_success_ordinaryOutcome_sound leftResult)
    (contractDecl_success_ordinaryOutcome_sound rightResult)

/-- Under an exact body contract, two declaration rejections have the same
declarative endpoint. -/
theorem contractDecl_reject_output_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ContractBodyRejects)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : contractDecl input = .reject leftFailure leftOutput)
    (rightResult : contractDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (contractDecl_exactOutcomeSpec_of_body bodyOutcomes).rejectOutputUnique
    (contractDecl_reject_ordinaryOutcome_sound leftResult)
    (contractDecl_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreContractDeclarationExactnessProperties
/-! Unconditional executable exactness for complete contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractInternals

/-- Public Core-expression field initializers need no exactness premise. -/
theorem contractFieldPublic_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.ContractFieldOrdinaryParses
        DeclarativeGrammar.CoreExpressionOrdinaryParses)
      (DeclarativeGrammar.ContractFieldRejects
        DeclarativeGrammar.CoreExpressionOrdinaryParses
        DeclarativeGrammar.CoreExpressionPublicRejects) :=
  DeclarativeGrammar.contractFieldPublicExactOutcomeSpec

/-- Public field successes agree on their complete AST and remainder. -/
theorem contractFieldPublic_success_result_unique
    {input leftOutput rightOutput : State} {left right : ContractField}
    (leftResult : contractField expression input = .ok left leftOutput)
    (rightResult : contractField expression input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractField_success_result_unique expression
    DeclarativeGrammar.CoreExpressionOrdinaryParses
    DeclarativeGrammar.CoreExpressionPublicRejects
    DeclarativeGrammar.coreExpressionPublicExactOutcomeSpec
    expression_success_ordinary_sound leftResult rightResult

/-- Public field rejections agree on their complete declarative endpoint. -/
theorem contractFieldPublic_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : contractField expression input = .reject leftFailure leftOutput)
    (rightResult : contractField expression input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractField_reject_output_unique expression
    DeclarativeGrammar.CoreExpressionOrdinaryParses
    DeclarativeGrammar.CoreExpressionPublicRejects
    DeclarativeGrammar.coreExpressionPublicExactOutcomeSpec
    expression_success_ordinary_sound expression_reject_ordinary_sound
    leftResult rightResult

/-- Attribute-free contract-member exactness needs no child premises. -/
theorem contractMemberCore_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects :=
  DeclarativeGrammar.contractMemberCoreExactOutcomeSpec

/-- Core-member successes agree without a supplied exact-outcome contract. -/
theorem contractMemberCore_success_result_unique_unconditional
    {input leftOutput rightOutput : State} {left right : ContractMember}
    (leftResult : contractMemberCore input = .ok left leftOutput)
    (rightResult : contractMemberCore input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractMemberCore_success_result_unique contractMemberCore_exactOutcomeSpec
    leftResult rightResult

/-- Core-member rejections agree without a supplied exact-outcome contract. -/
theorem contractMemberCore_reject_output_unique_unconditional
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : contractMemberCore input = .reject leftFailure leftOutput)
    (rightResult : contractMemberCore input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractMemberCore_reject_output_unique contractMemberCore_exactOutcomeSpec
    leftResult rightResult

/-- Derive-aware member exactness needs no core-member premise. -/
theorem contractMemberWithAttribute_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberOrdinaryParses
      DeclarativeGrammar.ContractMemberRejects :=
  DeclarativeGrammar.contractMemberExactOutcomeSpec

/-- Derive-aware member successes agree on their complete AST and remainder. -/
theorem contractMemberWithAttribute_success_result_unique
    {input leftOutput rightOutput : State} {left right : ContractMember}
    (leftResult : contractMemberWithAttribute input = .ok left leftOutput)
    (rightResult : contractMemberWithAttribute input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractMemberWithAttribute_exactOutcomeSpec.successResultUnique
    (contractMemberWithAttribute_success_ordinaryOutcome_sound leftResult)
    (contractMemberWithAttribute_success_ordinaryOutcome_sound rightResult)

/-- Derive-aware member rejections agree on their declarative endpoint. -/
theorem contractMemberWithAttribute_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : contractMemberWithAttribute input =
      .reject leftFailure leftOutput)
    (rightResult : contractMemberWithAttribute input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractMemberWithAttribute_exactOutcomeSpec.rejectOutputUnique
    (contractMemberWithAttribute_reject_ordinaryOutcome_sound leftResult)
    (contractMemberWithAttribute_reject_ordinaryOutcome_sound rightResult)

/-- Recovery-aware contract-body exactness needs no member premise. -/
theorem contractBody_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ContractBodyRejects :=
  DeclarativeGrammar.contractBodyExactOutcomeSpec

/-- Contract-body successes agree on their parser value and final remainder. -/
theorem contractBody_success_result_unique
    {input leftOutput rightOutput : State} {left right : ContractBody}
    (leftResult : contractBody input = .ok left leftOutput)
    (rightResult : contractBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractBody_success_result_unique_of_member
    DeclarativeGrammar.contractMemberExactOutcomeSpec leftResult rightResult

/-- Contract-body rejections agree on their complete declarative endpoint. -/
theorem contractBody_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : contractBody input = .reject leftFailure leftOutput)
    (rightResult : contractBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractBody_exactOutcomeSpec.rejectOutputUnique
    (contractBody_reject_ordinaryOutcome_sound leftResult)
    (contractBody_reject_ordinaryOutcome_sound rightResult)

end ContractInternals

/-- Complete contract-declaration exactness needs no body premise. -/
theorem contractDecl_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractDeclOrdinaryParses
      DeclarativeGrammar.ContractDeclRejects :=
  DeclarativeGrammar.contractDeclExactOutcomeSpec

/-- Complete contract successes agree on their complete AST and remainder. -/
theorem contractDecl_success_result_unique
    {input leftOutput rightOutput : State} {left right : ContractDecl}
    (leftResult : contractDecl input = .ok left leftOutput)
    (rightResult : contractDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractDecl_exactOutcomeSpec.successResultUnique
    (contractDecl_success_ordinaryOutcome_sound leftResult)
    (contractDecl_success_ordinaryOutcome_sound rightResult)

/-- Complete contract rejections agree on their complete declarative endpoint. -/
theorem contractDecl_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : contractDecl input = .reject leftFailure leftOutput)
    (rightResult : contractDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  contractDecl_exactOutcomeSpec.rejectOutputUnique
    (contractDecl_reject_ordinaryOutcome_sound leftResult)
    (contractDecl_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
end
