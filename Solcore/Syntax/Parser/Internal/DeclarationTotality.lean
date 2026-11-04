import Solcore.Syntax.Parser.Internal.ContractProofs
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.TypeTotality
import Solcore.Syntax.Parser.Internal.DelimitedTotality
import Solcore.Syntax.Parser.Internal.DeriveSoundness
import Solcore.Syntax.Parser.Internal.TypeAliasProofs
import Solcore.Syntax.Parser.Internal.EnumProofs
import Solcore.Syntax.Parser.Internal.PublicTermTotality
import Solcore.Syntax.Parser.Internal.ContractEntryProofs
import Solcore.Syntax.Parser.Internal.ImplProofs

/-!
Totality of the parsers of contracts and derive attributes: on valid input they make
progress and end in an ordinary outcome.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.ContractFieldTotalityProperties
/-! Valid-input totality laws local to contract fields. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- An optional initializer introduces no invariant beyond its expression parser. -/
theorem optionalFieldInitializer_invariantFreeOnValid
    (expressionParser : Parser Expr)
    (expressionFree : Parser.InvariantFreeOnValid expressionParser) :
    Parser.InvariantFreeOnValid
      (optionalFieldInitializer expressionParser) := by
  intro input inputValid
  by_cases present : isSymbol input .equal
  · rcases (symbol_ordinary .equal .contractMember) input with
      ⟨equal, afterEqual, equalResult⟩ |
      ⟨failure, rejected, equalResult⟩
    · have equalValid := symbol_validFor .equal .contractMember input inputValid
      rw [equalResult] at equalValid
      rcases expressionFree afterEqual equalValid.2.1 with
        ⟨value, final, expressionResult⟩ |
        ⟨failure, final, expressionResult⟩
      · exact Or.inl ⟨some value, final, by
          simp only [optionalFieldInitializer, getState, bind, present,
            ↓reduceIte, equalResult, expressionResult, pure]⟩
      · exact Or.inr ⟨failure, final, by
          simp only [optionalFieldInitializer, getState, bind, present,
            ↓reduceIte, equalResult, expressionResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [optionalFieldInitializer, getState, bind, present,
          ↓reduceIte, equalResult]⟩
  · exact Or.inl ⟨none, input, by
      have absent : isSymbol input .equal = false :=
        by
          cases found : isSymbol input .equal with
          | false => rfl
          | true => exact False.elim (present found)
      simp only [optionalFieldInitializer, getState, bind, absent, Bool.false_eq_true,
        ↓reduceIte, pure]⟩

theorem optionalFieldInitializer_ne_invariant
    (expressionParser : Parser Expr)
    (expressionFree : Parser.InvariantFreeOnValid expressionParser)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    optionalFieldInitializer expressionParser input ≠ .invariant error :=
  (optionalFieldInitializer_invariantFreeOnValid expressionParser
    expressionFree).ne_invariant input inputValid error

/--
A contract field introduces no invariant beyond its expression parser. Public
recursive type parsing and the final semicolon parser are already total.
-/
theorem contractField_invariantFreeOnValid
    (expressionParser : Parser Expr)
    (expressionFree : Parser.InvariantFreeOnValid expressionParser) :
    Parser.InvariantFreeOnValid (contractField expressionParser) := by
  intro input inputValid
  rcases (identifier_ordinary .contractMember) input with
    ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
  · have nameValid := identifier_validFor .contractMember input inputValid
    rw [nameResult] at nameValid
    rcases (symbol_ordinary .colon .contractMember) afterName with
      ⟨colon, afterColon, colonResult⟩ |
      ⟨failure, rejected, colonResult⟩
    · have colonValid := symbol_validFor .colon .contractMember afterName
        nameValid.2.1
      rw [colonResult] at colonValid
      rcases typeExpr_invariantFreeOnValid afterColon colonValid.2.1 with
        ⟨type, afterType, typeResult⟩ |
        ⟨failure, rejected, typeResult⟩
      · have typeValid := typeExpr_validFor afterColon colonValid.2.1
        rw [typeResult] at typeValid
        rcases optionalFieldInitializer_invariantFreeOnValid expressionParser
            expressionFree afterType typeValid.2.1 with
          ⟨initializer, afterInitializer, initializerResult⟩ |
          ⟨failure, rejected, initializerResult⟩
        · rcases (symbol_ordinary .semicolon .contractMember)
              afterInitializer with
            ⟨semicolon, final, semicolonResult⟩ |
            ⟨failure, rejected, semicolonResult⟩
          · exact Or.inl ⟨{
                span := SourceSpan.cover name.span semicolon.span
                value := { name, type, initializer }
              }, final, by
              simp only [contractField, bind, nameResult, colonResult,
                typeResult, initializerResult, semicolonResult, pure]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [contractField, bind, nameResult, colonResult,
                typeResult, initializerResult, semicolonResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [contractField, bind, nameResult, colonResult,
              typeResult, initializerResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [contractField, bind, nameResult, colonResult, typeResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [contractField, bind, nameResult, colonResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [contractField, bind, nameResult]⟩

theorem contractField_ne_invariant
    (expressionParser : Parser Expr)
    (expressionFree : Parser.InvariantFreeOnValid expressionParser)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    contractField expressionParser input ≠ .invariant error :=
  (contractField_invariantFreeOnValid expressionParser
    expressionFree).ne_invariant input inputValid error

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractRecoveryTotalityProperties
/-! Fuel adequacy and result classification for contract-member recovery. -/

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

/-- More fuel than remaining tokens rules out recovery-fuel exhaustion. -/
theorem recoverContractMemberAux_ok_of_remainingCount_lt
    (first last : SourceSpan) :
    ∀ fuel state, state.remainingCount < fuel →
      ∃ member final,
        recoverContractMemberAux first last fuel state = .ok member final := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      intro state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro state adequate
      unfold recoverContractMemberAux
      split
      · simp [finishRecoveredMember]
      · cases advanced : state.advance? with
        | none => simp [finishRecoveredMember]
        | some pair =>
            rcases pair with ⟨token, next⟩
            apply inductionHypothesis token.span next
            have shape := advance?_state_shape advanced
            have cursorBefore :=
              State.cursor_lt_endIndex_of_peek?_eq_some shape.1
            simp only [State.remainingCount, shape.2] at adequate ⊢
            omega

/-- The exact fuel chosen by the production parser is always adequate. -/
theorem recoverContractMemberAux_production_ok
    (first last : SourceSpan) (state : State) :
    ∃ member final,
      recoverContractMemberAux first last (state.remainingCount + 1) state =
        .ok member final :=
  recoverContractMemberAux_ok_of_remainingCount_lt first last
    (state.remainingCount + 1) state (by omega)

/-- Contract-member recovery has a total public result classification. -/
theorem recoverContractMember_total (state : State) :
    (∃ member final, recoverContractMember state = .ok member final) ∨
      (∃ failure final,
        recoverContractMember state = .reject failure final) := by
  unfold recoverContractMember
  cases advanced : state.advance? with
  | none =>
      right
      simp [rejectAt]
  | some pair =>
      rcases pair with ⟨token, next⟩
      left
      simpa only [advanced] using
        recoverContractMemberAux_production_ok token.span token.span next

/-- The public recovery parser cannot expose an internal invariant failure. -/
theorem recoverContractMember_ne_invariant (state : State)
    (error : ParserInvariantError) :
    recoverContractMember state ≠ .invariant error := by
  intro failed
  rcases recoverContractMember_total state with success | rejection
  · rcases success with ⟨member, final, recovered⟩
    rw [recovered] at failed
    contradiction
  · rcases rejection with ⟨failure, final, recovered⟩
    rw [recovered] at failed
    contradiction

/-- At the active window end recovery performs the parser's ordinary rejection. -/
theorem recoverContractMember_reject_of_atEnd (state : State)
    (atEnd : state.atEnd = true) :
    ∃ failure, recoverContractMember state = .reject failure state := by
  have cursorAtEnd : state.window.endIndex ≤ state.cursor := by
    simpa [State.atEnd] using atEnd
  simp [recoverContractMember, State.advance?, State.peek?,
    Nat.not_lt.mpr cursorAtEnd, rejectAt]

private theorem advance?_exists_of_valid_not_atEnd
    (state : State) (valid : state.ValidFor)
    (notEnd : state.atEnd = false) :
    ∃ token next, state.advance? = some (token, next) := by
  have cursorBefore : state.cursor < state.window.endIndex := by
    simpa [State.atEnd] using notEnd
  have cursorBound : state.cursor < state.tokens.size :=
    Nat.lt_of_lt_of_le cursorBefore valid.endIndex_le_size
  let token := state.tokens[state.cursor]'cursorBound
  have found : state.tokens[state.cursor]? = some token := by
    apply Array.getElem?_eq_some_iff.mpr
    exact ⟨cursorBound, rfl⟩
  refine ⟨token, { state with cursor := state.cursor + 1 }, ?_⟩
  simp [State.advance?, State.peek?, cursorBefore, found]

/-- A valid non-end state is recovered successfully, never rejected. -/
theorem recoverContractMember_ok_of_valid_not_atEnd
    (state : State) (valid : state.ValidFor)
    (notEnd : state.atEnd = false) :
    ∃ member final, recoverContractMember state = .ok member final := by
  rcases advance?_exists_of_valid_not_atEnd state valid notEnd with
    ⟨token, next, advanced⟩
  unfold recoverContractMember
  simpa only [advanced] using
    recoverContractMemberAux_production_ok token.span token.span next

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractBodyTotalityProperties
/-! Conditional totality for canonical contract-body accumulation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- The one remaining invariant-freedom premise at the member boundary. -/
def ContractMemberInvariantFreeOnValid : Prop :=
  ∀ input, input.ValidFor → ∀ error,
    contractMemberWithAttribute input ≠ .invariant error

private theorem acceptToken_ordinary (expected : ParseExpectation)
    (context : ParseContext) (accepts : TokenKind → Bool) (state : State) :
    (∃ token final,
      acceptToken expected context accepts state = .ok token final) ∨
      (∃ failure final,
        acceptToken expected context accepts state = .reject failure final) := by
  cases result : acceptToken expected context accepts state with
  | ok token final => exact Or.inl ⟨token, final, rfl⟩
  | reject failure final => exact Or.inr ⟨failure, final, rfl⟩
  | invariant error =>
      unfold acceptToken at result
      cases found : state.peek? with
      | none => simp [found, rejectAt] at result
      | some token =>
          simp only [found] at result
          split at result
          · contradiction
          · simp [rejectAt] at result

private theorem rewindAfterMemberReject_validFor
    {input failedState : State}
    (inputValid : input.ValidFor) (failedValid : failedState.ValidFor)
    (windowEq : failedState.window = input.window) :
    ({ failedState with cursor := input.cursor } : State).ValidFor := {
  tokens := failedValid.tokens
  cursor_le_endIndex := by
    simpa [windowEq] using inputValid.cursor_le_endIndex
  endIndex_le_size := failedValid.endIndex_le_size
  endByte_le_source := failedValid.endByte_le_source
  endByte_boundary := failedValid.endByte_boundary
  diagnosticsRev := failedValid.diagnosticsRev
}

private theorem remainingCount_lt_after_strict_progress
    {input next : State} {fuel : Nat}
    (nextValid : next.ValidFor)
    (windowEq : next.window = input.window)
    (progress : input.cursor < next.cursor)
    (adequate : input.remainingCount < fuel + 1) :
    next.remainingCount < fuel := by
  have nextCursorBound : next.cursor ≤ input.window.endIndex := by
    simpa [windowEq] using nextValid.cursor_le_endIndex
  have endIndexEq : next.window.endIndex = input.window.endIndex :=
    congrArg TokenWindow.endIndex windowEq
  simp only [State.remainingCount] at adequate ⊢
  rw [endIndexEq]
  omega

private theorem closeContractBody_ordinary (opening : Token)
    (membersRev : List ContractMember) (state : State) :
    (∃ body final,
      closeContractBody opening membersRev state = .ok body final) ∨
      (∃ failure final,
        closeContractBody opening membersRev state = .reject failure final) := by
  rcases acceptToken_ordinary (.symbol .rightBrace) .topItem
      (fun kind => kind == .symbol .rightBrace) state with success | rejection
  · rcases success with ⟨closing, next, closingResult⟩
    left
    unfold closeContractBody
    simp only [symbol, closingResult, bind, pure]
    exact ⟨_, _, rfl⟩
  · rcases rejection with ⟨failure, next, closingResult⟩
    right
    unfold closeContractBody
    simp only [symbol, closingResult, bind]
    exact ⟨failure, next, rfl⟩

/--
With an ordinary member parser and adequate fuel, contract accumulation has
only an ordinary success or rejection.  Its fuel and no-progress invariants
are therefore unreachable.
-/
theorem contractMembers_ordinary_of_remainingCount_lt
    (memberInvariantFree : ContractMemberInvariantFreeOnValid)
    (opening : Token) :
    ∀ fuel membersRev input,
      input.ValidFor → input.remainingCount < fuel →
      (∃ body final,
        contractMembers opening fuel membersRev input = .ok body final) ∨
        (∃ failure final,
          contractMembers opening fuel membersRev input =
            .reject failure final) := by
  intro fuel
  induction fuel with
  | zero =>
      intro membersRev input inputValid adequate
      omega
  | succ fuel inductionHypothesis =>
      intro membersRev input inputValid adequate
      unfold contractMembers
      split
      · exact closeContractBody_ordinary opening membersRev input
      · rename_i notClosing
        split
        · rename_i atEnd
          have cursorAtEnd : input.window.endIndex ≤ input.cursor := by
            simpa [State.atEnd] using atEnd
          have peekNone : input.peek? = none := by
            unfold State.peek?
            simp [Nat.not_lt_of_ge cursorAtEnd]
          right
          simp [symbol, acceptToken, peekNone, rejectAt]
        · rename_i notAtEnd
          have memberReply :=
            contractMemberWithAttribute_canonical_contract.validFor
              input inputValid
          have memberWindow :=
            contractMemberWithAttribute_canonical_contract.preservesTokenWindow
              input
          cases memberResult : contractMemberWithAttribute input with
          | invariant error =>
              exact False.elim
                (memberInvariantFree input inputValid error memberResult)
          | ok member next =>
              rw [memberResult] at memberReply memberWindow
              have progress :=
                contractMemberWithAttribute_cursor_lt_onSuccess memberResult
              have nextAdequate := remainingCount_lt_after_strict_progress
                memberReply.2.1 memberWindow.2 progress adequate
              have recursive := inductionHypothesis (member :: membersRev)
                next memberReply.2.1 nextAdequate
              dsimp only
              split
              · exact recursive
              · omega
          | reject failure failedState =>
              rw [memberResult] at memberReply memberWindow
              let rewound : State := {
                failedState with cursor := input.cursor
              }
              have rewoundValid : rewound.ValidFor :=
                rewindAfterMemberReject_validFor inputValid memberReply.2.1
                  memberWindow.2
              have rewoundNotAtEnd : rewound.atEnd = false := by
                simpa [rewound, State.atEnd, memberWindow.2] using notAtEnd
              dsimp only
              split
              · right
                exact ⟨failure, rewound, rfl⟩
              · rcases recoverContractMember_ok_of_valid_not_atEnd
                    rewound rewoundValid rewoundNotAtEnd with
                  ⟨recovered, next, recoveryResult⟩
                have recoveryReply :=
                  recoverContractMember_validFor rewound rewoundValid
                rw [recoveryResult] at recoveryReply
                have recoveryWindow :=
                  recoverContractMember_preservesTokenWindow rewound
                rw [recoveryResult] at recoveryWindow
                have rewoundAdequate :
                    rewound.remainingCount < fuel + 1 := by
                  simpa only [State.remainingCount, rewound, memberWindow.2]
                    using adequate
                have nextAdequate := remainingCount_lt_after_strict_progress
                  recoveryReply.2.1 recoveryWindow.2
                  (recoverContractMember_cursor_lt_onSuccess recoveryResult)
                  rewoundAdequate
                have recursive := inductionHypothesis
                  (recovered :: membersRev) next recoveryReply.2.1
                  nextAdequate
                have recoveryResult' :
                    recoverContractMember {
                      failedState with cursor := input.cursor
                    } = .ok recovered next := by
                  simpa [rewound] using recoveryResult
                simpa only [recoveryResult'] using recursive

/-- The production loop fuel is adequate for every valid body state. -/
theorem contractMembers_production_ordinary
    (memberInvariantFree : ContractMemberInvariantFreeOnValid)
    (opening : Token) (membersRev : List ContractMember)
    (input : State) (inputValid : input.ValidFor) :
    (∃ body final,
      contractMembers opening (input.remainingCount + 1) membersRev input =
        .ok body final) ∨
      (∃ failure final,
        contractMembers opening (input.remainingCount + 1) membersRev input =
          .reject failure final) :=
  contractMembers_ordinary_of_remainingCount_lt memberInvariantFree opening
    (input.remainingCount + 1) membersRev input inputValid (by omega)

/-- A valid contract body has only an ordinary public parser result. -/
theorem contractBody_ordinary
    (memberInvariantFree : ContractMemberInvariantFreeOnValid)
    (input : State) (inputValid : input.ValidFor) :
    (∃ body final, contractBody input = .ok body final) ∨
      (∃ failure final, contractBody input = .reject failure final) := by
  rcases acceptToken_ordinary (.symbol .leftBrace) .topItem
      (fun kind => kind == .symbol .leftBrace) input with success | rejection
  · rcases success with ⟨opening, next, openingResult⟩
    have openingResult' : symbol .leftBrace .topItem input =
        .ok opening next := openingResult
    have openingReply := symbol_validFor .leftBrace .topItem input inputValid
    rw [openingResult'] at openingReply
    unfold contractBody
    simp only [openingResult']
    exact contractMembers_production_ordinary memberInvariantFree opening []
      next openingReply.2.1
  · rcases rejection with ⟨failure, next, openingResult⟩
    have openingResult' : symbol .leftBrace .topItem input =
        .reject failure next := openingResult
    right
    unfold contractBody
    simp only [openingResult']
    exact ⟨failure, next, rfl⟩

/-- The body parser cannot expose an invariant under the single member premise. -/
theorem contractBody_ne_invariant
    (memberInvariantFree : ContractMemberInvariantFreeOnValid)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    contractBody input ≠ .invariant error := by
  intro failed
  rcases contractBody_ordinary memberInvariantFree input inputValid with
    ⟨body, final, result⟩ | ⟨failure, final, result⟩ <;>
      rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveTargetTotalityProperties
/-! Resource and ordinary-result contracts for canonical derive targets. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace DeriveTargetInternals

/-- A derive component has only an ordinary success or rejection. -/
theorem deriveComponent_ordinary (state : State) :
    (∃ name final, deriveComponent state = .ok name final) ∨
      (∃ failure final,
        deriveComponent state = .reject failure final) := by
  unfold deriveComponent
  cases found : state.peek? with
  | none =>
      right
      simp [rejectAt]
  | some token =>
      cases reserved : reservedDeriveKeyword? token.value with
      | some keyword =>
          left
          simp [reserved]
      | none =>
          simpa only [reserved] using identifier_ordinary .topItem state

/-- A derive component can never expose a parser invariant. -/
theorem deriveComponent_ne_invariant (state : State)
    (error : ParserInvariantError) :
    deriveComponent state ≠ .invariant error := by
  intro failed
  rcases deriveComponent_ordinary state with
    ⟨name, final, result⟩ | ⟨failure, final, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Component success advances exactly one token and preserves the window. -/
theorem deriveComponent_ok_cursor_window
    {input final : State} {name : Identifier}
    (parsed : deriveComponent input = .ok name final) :
    final.cursor = input.cursor + 1 ∧ final.window = input.window := by
  unfold deriveComponent at parsed
  cases found : input.peek? with
  | none => simp [found, rejectAt] at parsed
  | some token =>
      simp only [found] at parsed
      cases reserved : reservedDeriveKeyword? token.value with
      | some keyword =>
          simp only [reserved] at parsed
          cases parsed
          simp [State.emit]
      | none =>
          simp only [reserved] at parsed
          have shape := identifier_ok_state_shape .topItem parsed
          have window := identifier_preservesTokenWindow .topItem input
          rw [parsed] at window
          exact ⟨shape.choose_spec.2.2.2, window.2⟩

private theorem remainingCount_lt_after_dot_component
    {input afterDot next : State} {dot : Token} {component : Identifier}
    {fuel : Nat}
    (dotResult : symbol .dot .topItem input = .ok dot afterDot)
    (componentResult : deriveComponent afterDot = .ok component next)
    (adequate : input.remainingCount < fuel + 1) :
    next.remainingCount < fuel := by
  have dotShape := symbol_ok_state_shape .dot .topItem dotResult
  have componentShape := deriveComponent_ok_cursor_window componentResult
  have componentFound : ∃ token, afterDot.peek? = some token := by
    unfold deriveComponent at componentResult
    cases found : afterDot.peek? with
    | none => simp [found, rejectAt] at componentResult
    | some token => exact ⟨token, rfl⟩
  rcases componentFound with ⟨token, found⟩
  have afterDotBeforeEnd :=
    State.cursor_lt_endIndex_of_peek?_eq_some found
  have dotCursorEq : afterDot.cursor = input.cursor + 1 := by
    rw [dotShape.2]
  have dotWindowEq : afterDot.window = input.window := by
    rw [dotShape.2]
  have afterDotBeforeEnd' :
      input.cursor + 1 < input.window.endIndex := by
    simpa [dotCursorEq, dotWindowEq] using afterDotBeforeEnd
  have inputTwoBound : input.cursor + 2 ≤ input.window.endIndex := by
    omega
  have nextCursorEq : next.cursor = input.cursor + 2 := by
    rw [componentShape.1, dotCursorEq]
  have nextEndIndexEq :
      next.window.endIndex = input.window.endIndex := by
    exact congrArg TokenWindow.endIndex
      (componentShape.2.trans dotWindowEq)
  simp only [State.remainingCount] at adequate ⊢
  rw [nextEndIndexEq, nextCursorEq]
  omega

/-- Adequate fuel makes the dotted-tail loop return only ordinary results. -/
theorem deriveTargetTail_ordinary_of_remainingCount_lt
    (first : Identifier) :
    ∀ fuel last tailRev state,
      state.remainingCount < fuel →
      (∃ target final,
        deriveTargetTail first fuel last tailRev state = .ok target final) ∨
        (∃ failure final,
          deriveTargetTail first fuel last tailRev state =
            .reject failure final) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro last tailRev state adequate
      unfold deriveTargetTail
      split
      · cases dotResult : symbol .dot .topItem state with
        | invariant error =>
            exact False.elim (symbol_ne_invariant .dot .topItem state
              error dotResult)
        | reject failure rejected =>
            right
            exact ⟨failure, rejected, rfl⟩
        | ok dot afterDot =>
            cases componentResult : deriveComponent afterDot with
            | invariant error =>
                exact False.elim
                  (deriveComponent_ne_invariant afterDot error componentResult)
            | reject failure rejected =>
                right
                simp [componentResult]
            | ok component next =>
                have nextAdequate := remainingCount_lt_after_dot_component
                  dotResult componentResult adequate
                simpa only [componentResult] using
                  inductionHypothesis component (component :: tailRev)
                    next nextAdequate
      · left
        exact ⟨_, _, rfl⟩

/-- The production fuel for a derive-target tail is always adequate. -/
theorem deriveTargetTail_production_ordinary
    (first last : Identifier) (tailRev : List Identifier) (state : State) :
    (∃ target final,
      deriveTargetTail first (state.remainingCount + 1) last tailRev state =
        .ok target final) ∨
      (∃ failure final,
        deriveTargetTail first (state.remainingCount + 1) last tailRev state =
          .reject failure final) :=
  deriveTargetTail_ordinary_of_remainingCount_lt first
    (state.remainingCount + 1) last tailRev state (by omega)

/-- An adequately fueled derive-target tail cannot expose an invariant. -/
theorem deriveTargetTail_ne_invariant_of_remainingCount_lt
    (first last : Identifier) (tailRev : List Identifier)
    (fuel : Nat) (state : State)
    (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    deriveTargetTail first fuel last tailRev state ≠ .invariant error := by
  intro failed
  rcases deriveTargetTail_ordinary_of_remainingCount_lt first fuel last tailRev
      state adequate with
    ⟨target, final, result⟩ | ⟨failure, final, result⟩ <;>
      rw [result] at failed <;> contradiction

end DeriveTargetInternals

open DeriveTargetInternals

/-- Public derive-target parsing has only an ordinary result. -/
theorem deriveTarget_ordinary (state : State) :
    (∃ target final, deriveTarget state = .ok target final) ∨
      (∃ failure final, deriveTarget state = .reject failure final) := by
  rcases deriveComponent_ordinary state with success | rejection
  · rcases success with ⟨first, next, firstResult⟩
    unfold deriveTarget
    simp only [firstResult]
    exact deriveTargetTail_production_ordinary first first [] next
  · rcases rejection with ⟨failure, next, firstResult⟩
    right
    unfold deriveTarget
    simp only [firstResult]
    exact ⟨failure, next, rfl⟩

/-- Public derive-target parsing cannot expose an internal invariant. -/
theorem deriveTarget_ne_invariant (state : State)
    (error : ParserInvariantError) :
    deriveTarget state ≠ .invariant error := by
  intro failed
  rcases deriveTarget_ordinary state with
    ⟨target, final, result⟩ | ⟨failure, final, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Derive targets instantiate the generic strict delimited-element boundary. -/
theorem deriveTarget_elementTotalityContract :
    ElementTotalityContract deriveTarget := {
  validFor := deriveTarget_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := deriveTarget_preservesTokenWindow
  cursorLtOnSuccess := fun parsed =>
    (deriveTarget_ok_state_shape parsed).choose_spec.2.2.2
  invariantFree := fun input _ error =>
    deriveTarget_ne_invariant input error
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveRecoveryTotalityProperties
/-! Fuel adequacy and ordinary control flow for derive recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.DeriveAttributeInternals

/-- More fuel than remaining tokens makes the recovery tail ordinary. -/
theorem recoverTail_ordinary_of_remainingCount_lt
    (hash last : SourceSpan) :
    ∀ fuel state, state.remainingCount < fuel →
      (∃ derive next,
        recoverTail hash last fuel state = .ok derive next) ∨
      (∃ failure next,
        recoverTail hash last fuel state = .reject failure next) := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      intro state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro state adequate
      unfold recoverTail
      split
      · cases closingResult : symbol .rightBracket .topItem state with
        | ok closing next =>
            dsimp only
            exact Or.inl ⟨_, _, rfl⟩
        | reject failure rejected =>
            exact Or.inr ⟨failure, rejected, rfl⟩
        | invariant error =>
            exact False.elim
              (symbol_ne_invariant .rightBracket .topItem state error
                closingResult)
      · split
        · exact Or.inl ⟨_, _, rfl⟩
        · cases advanced : state.advance? with
          | none => exact Or.inl ⟨_, _, rfl⟩
          | some pair =>
              rcases pair with ⟨token, next⟩
              change
                (∃ derive final,
                  recoverTail hash token.span fuel next = .ok derive final) ∨
                (∃ failure final,
                  recoverTail hash token.span fuel next =
                    .reject failure final)
              apply inductionHypothesis token.span next
              unfold State.advance? at advanced
              cases found : state.peek? with
              | none => simp [found] at advanced
              | some current =>
                  simp only [found, Option.map_some] at advanced
                  cases advanced
                  have cursorBeforeEnd :=
                    State.cursor_lt_endIndex_of_peek?_eq_some found
                  simp only [State.remainingCount] at adequate ⊢
                  omega

/-- Adequate derive recovery fuel excludes its internal invariant branch. -/
theorem recoverTail_ne_invariant_of_remainingCount_lt
    (hash last : SourceSpan) (fuel : Nat) (state : State)
    (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    recoverTail hash last fuel state ≠ .invariant error := by
  intro failed
  rcases recoverTail_ordinary_of_remainingCount_lt hash last fuel state
      adequate with
    ⟨derive, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- The exact production fuel chosen for a recovery tail is sufficient. -/
theorem recoverTail_production_ordinary
    (hash last : SourceSpan) (state : State) :
    (∃ derive next,
      recoverTail hash last (state.remainingCount + 1) state =
        .ok derive next) ∨
      (∃ failure next,
        recoverTail hash last (state.remainingCount + 1) state =
          .reject failure next) :=
  recoverTail_ordinary_of_remainingCount_lt hash last
    (state.remainingCount + 1) state (by omega)

/-- The proof-visible recovered derive parser is ordinary on every input. -/
theorem recovered_ordinary : Parser.Ordinary recovered := by
  intro input
  unfold recovered
  cases hashResult : symbol .hash .topItem input with
  | ok hash afterHash =>
      dsimp only
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | ok opening next =>
          dsimp only
          exact recoverTail_production_ordinary hash.span opening.span next
      | reject failure rejected =>
          exact Or.inr ⟨failure, rejected, rfl⟩
      | invariant error =>
          exact False.elim
            (symbol_ne_invariant .leftBracket .topItem afterHash error
              openingResult)
  | reject failure rejected =>
      exact Or.inr ⟨failure, rejected, rfl⟩
  | invariant error =>
      exact False.elim
        (symbol_ne_invariant .hash .topItem input error hashResult)

/-- Recovered derive parsing cannot expose fuel or primitive invariants. -/
theorem recovered_ne_invariant (input : State)
    (error : ParserInvariantError) :
    recovered input ≠ .invariant error :=
  recovered_ordinary.ne_invariant input error

end Solcore.Syntax.Parser.DeriveAttributeInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveAttributeTotalityProperties
/-! Conditional totality for canonical derive attributes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.DeriveAttributeInternals

/-- The proof-visible valid derive path is ordinary on valid input. -/
theorem valid_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ derive next, valid input = .ok derive next) ∨
      (∃ failure next, valid input = .reject failure next) := by
  unfold valid
  cases hashResult : symbol .hash .topItem input with
  | invariant error =>
      exact False.elim
        (symbol_ne_invariant .hash .topItem input error hashResult)
  | reject failure rejected =>
      right
      simp only [bind, hashResult]
      exact ⟨failure, rejected, rfl⟩
  | ok hash afterHash =>
      have hashReply := symbol_validFor .hash .topItem input inputValid
      rw [hashResult] at hashReply
      simp only [bind, hashResult]
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | invariant error =>
          exact False.elim
            (symbol_ne_invariant .leftBracket .topItem afterHash error
              openingResult)
      | reject failure rejected =>
          simp only
          exact Or.inr ⟨failure, rejected, rfl⟩
      | ok opening afterOpening =>
          have openingReply := symbol_validFor .leftBracket .topItem
            afterHash hashReply.2.1
          rw [openingResult] at openingReply
          simp only
          cases deriveResult : contextual .derive .topItem afterOpening with
          | invariant error =>
              exact False.elim
                (contextual_ne_invariant .derive .topItem afterOpening error
                  deriveResult)
          | reject failure rejected =>
              simp only
              exact Or.inr ⟨failure, rejected, rfl⟩
          | ok deriveKeyword afterDerive =>
              have deriveReply := contextual_validFor .derive .topItem
                afterOpening openingReply.2.1
              rw [deriveResult] at deriveReply
              simp only
              cases targetsResult : delimitedNoTrailing .leftParen .rightParen
                  true deriveTarget .topItem .topLevel afterDerive with
              | invariant error =>
                  exact False.elim
                    (delimitedNoTrailing_ne_invariant .leftParen .rightParen
                      true deriveTarget .topItem .topLevel
                      deriveTarget_elementTotalityContract afterDerive
                      deriveReply.2.1 error targetsResult)
              | reject failure rejected =>
                  simp only
                  exact Or.inr ⟨failure, rejected, rfl⟩
              | ok targets afterTargets =>
                  simp only
                  cases closingResult : symbol .rightBracket .topItem
                      afterTargets with
                  | invariant error =>
                      exact False.elim
                        (symbol_ne_invariant .rightBracket .topItem
                          afterTargets error closingResult)
                  | reject failure rejected =>
                      simp only
                      exact Or.inr ⟨failure, rejected, rfl⟩
                  | ok closing afterClosing =>
                      simp only
                      by_cases empty : targets.elements = []
                      · left
                        simp [empty, emitDiagnostic, modifyState, pure]
                      · left
                        simp [empty, pure]

/-- The valid derive path cannot expose an invariant on valid input. -/
theorem valid_ne_invariant (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    valid input ≠ .invariant error := by
  intro failed
  rcases valid_ordinary input inputValid with
    ⟨derive, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.DeriveAttributeInternals

namespace Solcore.Syntax.Parser

/-- Public derive-attribute parsing is ordinary on every valid input. -/
theorem deriveAttribute_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ derive next, deriveAttribute input = .ok derive next) ∨
      (∃ failure next,
        deriveAttribute input = .reject failure next) := by
  unfold deriveAttribute orElse
  cases validResult : DeriveAttributeInternals.valid input with
  | ok derive next => exact Or.inl ⟨derive, next, rfl⟩
  | invariant error =>
      exact False.elim
        (DeriveAttributeInternals.valid_ne_invariant input inputValid error
          validResult)
  | reject failure rejected =>
      simpa only using DeriveAttributeInternals.recovered_ordinary input

/-- Public derive-attribute parsing cannot expose an invariant on valid input. -/
theorem deriveAttribute_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    deriveAttribute input ≠ .invariant error := by
  intro failed
  rcases deriveAttribute_ordinary input inputValid with
    ⟨derive, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Derive attributes instantiate the generic strict delimited-element boundary. -/
theorem deriveAttribute_elementTotalityContract :
    ElementTotalityContract deriveAttribute := {
  validFor := deriveAttribute_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := deriveAttribute_preservesTokenWindow
  cursorLtOnSuccess := deriveAttribute_cursor_lt_onSuccess
  invariantFree := fun input inputValid error =>
    deriveAttribute_ne_invariant input inputValid error
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractMemberTotalityProperties
/-! Conditional totality for canonical contract-member dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Mapping a successful declaration cannot introduce an invariant reply. -/
theorem mapMember_invariantFreeOnValid {alpha : Type}
    (parser : Parser alpha) (wrap : alpha → ContractMember)
    (invariantFree : Parser.InvariantFreeOnValid parser) :
    Parser.InvariantFreeOnValid (mapMember parser wrap) := by
  intro input inputValid
  rcases invariantFree input inputValid with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩
  · left
    exact ⟨wrap value, next, by
      unfold mapMember
      simp only [bind, result, pure]⟩
  · right
    exact ⟨failure, next, by
      unfold mapMember
      simp only [bind, result]⟩

/-- The five declaration parsers selected by contract-member dispatch. -/
structure ContractMemberTotalityContract : Prop where
  field : Parser.InvariantFreeOnValid (contractField expression)
  function : Parser.InvariantFreeOnValid (functionDecl .contract)
  constructor : Parser.InvariantFreeOnValid constructorDecl
  fallback : Parser.InvariantFreeOnValid fallbackDecl
  enum : Parser.InvariantFreeOnValid (enumDecl none)

/-- The state-selected plain member parser inherits exactly those five inputs. -/
theorem contractMemberParser_invariantFreeOnValid
    (contract : ContractMemberTotalityContract) (state : State) :
    Parser.InvariantFreeOnValid (contractMemberParser state) := by
  unfold contractMemberParser
  split
  · exact mapMember_invariantFreeOnValid _ wrapField contract.field
  split
  · exact mapMember_invariantFreeOnValid _ wrapContractFunction
      contract.function
  split
  · exact mapMember_invariantFreeOnValid _ wrapConstructor
      contract.constructor
  split
  · exact mapMember_invariantFreeOnValid _ wrapFallback contract.fallback
  split
  · exact mapMember_invariantFreeOnValid _ wrapContractTypeAlias
      typeAlias_invariantFreeOnValid
  split
  · exact mapMember_invariantFreeOnValid _ wrapContractEnum contract.enum
  · exact Parser.rejectAt_invariantFreeOnValid
      (alpha := ContractMember) { head := .topItem, tail := [] }
      .contractMember

/-- Plain contract-member dispatch is invariant-free on valid input. -/
theorem contractMemberCore_invariantFreeOnValid
    (contract : ContractMemberTotalityContract) :
    Parser.InvariantFreeOnValid contractMemberCore := by
  intro input inputValid
  exact contractMemberParser_invariantFreeOnValid contract input
    input inputValid

/-- Attaching a derive attribute is a total state update. -/
theorem attachContractDerive_invariantFreeOnValid
    (derive : DeriveAttribute) (member : ContractMember) :
    Parser.InvariantFreeOnValid (attachContractDerive derive member) := by
  intro input _inputValid
  rcases member with ⟨span, comments, value⟩
  cases value <;> left <;>
    simp [attachContractDerive, emitDiagnostic, modifyState, bind, pure]

/-- Derive-aware member dispatch inherits only the same five branch inputs. -/
theorem contractMemberWithAttribute_invariantFreeOnValid
    (contract : ContractMemberTotalityContract) :
    Parser.InvariantFreeOnValid contractMemberWithAttribute := by
  intro input inputValid
  unfold contractMemberWithAttribute
  by_cases attributed : isSymbol input .hash
  · simp only [attributed, if_true]
    have deriveReply := deriveAttribute_validFor input inputValid
    rcases deriveAttribute_ordinary input inputValid with
      ⟨derive, afterDerive, deriveResult⟩ |
      ⟨failure, rejected, deriveResult⟩
    · rw [deriveResult] at deriveReply
      have memberReply := contractMemberCore_canonical_contract.validFor
        afterDerive deriveReply.2.1
      rcases contractMemberCore_invariantFreeOnValid contract afterDerive
          deriveReply.2.1 with
        ⟨member, next, memberResult⟩ |
        ⟨failure, rejected, memberResult⟩
      · rw [memberResult] at memberReply
        rcases attachContractDerive_invariantFreeOnValid derive member next
            memberReply.2.1 with
          ⟨attached, final, attachedResult⟩ |
          ⟨failure, rejected, attachedResult⟩
        · left
          exact ⟨attached, final, by
            simp only [deriveResult, memberResult, attachedResult]⟩
        · right
          exact ⟨failure, rejected, by
            simp only [deriveResult, memberResult, attachedResult]⟩
      · right
        exact ⟨failure, rejected, by
          simp only [deriveResult, memberResult]⟩
    · right
      exact ⟨failure, rejected, by simp only [deriveResult]⟩
  · simpa [attributed] using
      contractMemberCore_invariantFreeOnValid contract input inputValid

/-- No invariant can escape derive-aware member parsing under five inputs. -/
theorem contractMemberWithAttribute_ne_invariant
    (contract : ContractMemberTotalityContract)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    contractMemberWithAttribute input ≠ .invariant error :=
  (contractMemberWithAttribute_invariantFreeOnValid contract).ne_invariant
    input inputValid error

/-- Convert the five-field contract to the contract-body loop premise. -/
theorem contractMemberInvariantFree_of_totalityContract
    (contract : ContractMemberTotalityContract) :
    ContractMemberInvariantFreeOnValid := by
  intro input inputValid error
  exact contractMemberWithAttribute_ne_invariant contract input inputValid error

/-- Contract-body parsing is ordinary under exactly the five member inputs. -/
theorem contractBody_ordinary_of_memberTotalityContract
    (contract : ContractMemberTotalityContract)
    (input : State) (inputValid : input.ValidFor) :
    (∃ body final, contractBody input = .ok body final) ∨
      (∃ failure final, contractBody input = .reject failure final) :=
  contractBody_ordinary
    (contractMemberInvariantFree_of_totalityContract contract) input inputValid

/-- Contract-body invariants are unreachable under the same five inputs. -/
theorem contractBody_ne_invariant_of_memberTotalityContract
    (contract : ContractMemberTotalityContract)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    contractBody input ≠ .invariant error :=
  contractBody_ne_invariant
    (contractMemberInvariantFree_of_totalityContract contract)
    input inputValid error

end Solcore.Syntax.Parser.ContractInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PublicContractFieldTotalityProperties
/-! Unconditional totality for canonical production contract fields. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Production fields inherit unconditional totality from public expressions. -/
theorem contractField_invariantFreeOnValid :
    Parser.InvariantFreeOnValid
      (ContractInternals.contractField expression) :=
  ContractInternals.contractField_invariantFreeOnValid expression
    expression_invariantFreeOnValid

/-- No internal invariant can escape production contract-field parsing. -/
theorem contractField_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    ContractInternals.contractField expression input ≠ .invariant error :=
  contractField_invariantFreeOnValid.ne_invariant input inputValid error

/-- A successful production field strictly consumes its leading name. -/
theorem contractField_cursor_lt_onSuccess
    {input final : State} {field : ContractField}
    (parsed : ContractInternals.contractField expression input =
      .ok field final) :
    input.cursor < final.cursor := by
  have mapped : ContractInternals.mapMember
      (ContractInternals.contractField expression)
      ContractInternals.wrapField input =
        .ok (ContractInternals.wrapField field) final := by
    unfold ContractInternals.mapMember
    simp only [bind, parsed, pure]
  exact ContractInternals.contractFieldMember_cursor_lt_onSuccess mapped

/-- Production field syntax/state laws paired with unconditional totality. -/
theorem contractField_elementTotalityContract :
    ElementTotalityContract
      (ContractInternals.contractField expression) := {
  validFor := (ContractInternals.contractField_validFor expression
    (Expr.ValidFor CoreStatement.ValidFor)
    expression_canonical_contract.validFor
    expression_elementTotalityContract.preservesTokenWindow
    expression_canonical_contract.cursorMonotoneOnSuccess).mono
      (fun _ _ _ => trivial)
  preservesTokenWindow :=
    ContractInternals.contractField_preservesTokenWindow expression
      expression_elementTotalityContract.preservesTokenWindow
  cursorLtOnSuccess := contractField_cursor_lt_onSuccess
  invariantFree := contractField_ne_invariant
}

namespace ContractInternals

/--
Fill the production field and enum branches while keeping the three unfinished
member families explicit assumptions.
-/
theorem contractMemberTotalityContract_of_remainingBranches
    (functionFree : Parser.InvariantFreeOnValid (functionDecl .contract))
    (constructorFree : Parser.InvariantFreeOnValid constructorDecl)
    (fallbackFree : Parser.InvariantFreeOnValid fallbackDecl) :
    ContractMemberTotalityContract := {
  field := Solcore.Syntax.Parser.contractField_invariantFreeOnValid
  function := functionFree
  constructor := constructorFree
  fallback := fallbackFree
  enum := enumDecl_invariantFreeOnValid none
}

end ContractInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ContractDeclarationTotalityProperties
/-! Unconditional totality from contract members through contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractInternals

/-- All five production contract-member branches are invariant-free. -/
theorem productionContractMemberTotalityContract :
    ContractMemberTotalityContract :=
  contractMemberTotalityContract_of_remainingBranches
    (functionDecl_invariantFreeOnValid .contract)
    constructorDecl_invariantFreeOnValid
    fallbackDecl_invariantFreeOnValid

/-- Plain production member dispatch has only ordinary outcomes. -/
theorem productionContractMemberCore_invariantFreeOnValid :
    Parser.InvariantFreeOnValid contractMemberCore :=
  contractMemberCore_invariantFreeOnValid
    productionContractMemberTotalityContract

/-- Derive-aware production member dispatch has only ordinary outcomes. -/
theorem productionContractMemberWithAttribute_invariantFreeOnValid :
    Parser.InvariantFreeOnValid contractMemberWithAttribute :=
  contractMemberWithAttribute_invariantFreeOnValid
    productionContractMemberTotalityContract

theorem productionContractMemberWithAttribute_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    contractMemberWithAttribute input ≠ .invariant error :=
  productionContractMemberWithAttribute_invariantFreeOnValid.ne_invariant
    input inputValid error

/-- The concrete member contract discharges the contract-body loop premise. -/
theorem productionContractMemberInvariantFreeOnValid :
    ContractMemberInvariantFreeOnValid :=
  contractMemberInvariantFree_of_totalityContract
    productionContractMemberTotalityContract

/-- Production contract bodies have only ordinary outcomes on valid input. -/
theorem productionContractBody_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ body final, contractBody input = .ok body final) ∨
      (∃ failure final, contractBody input = .reject failure final) :=
  contractBody_ordinary productionContractMemberInvariantFreeOnValid
    input inputValid

theorem contractBody_invariantFreeOnValid :
    Parser.InvariantFreeOnValid contractBody :=
  productionContractBody_ordinary

theorem productionContractBody_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    contractBody input ≠ .invariant error :=
  contractBody_invariantFreeOnValid.ne_invariant input inputValid error

end ContractInternals

/-- Every production stage of a contract declaration is invariant-free. -/
theorem contractDecl_invariantFreeOnValid :
    Parser.InvariantFreeOnValid contractDecl := by
  unfold contractDecl
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .contractKw .topItem)
    (keyword_ordinary .contractKw .topItem).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid
    (identifier_validFor .topItem)
    (identifier_ordinary .topItem).invariantFreeOnValid
  intro name
  apply Parser.bind_invariantFreeOnValid
    optionalGenericParameters_validFor
    optionalGenericParameters_invariantFreeOnValid
  intro genericParameters
  apply Parser.bind_invariantFreeOnValid
    ContractInternals.contractBody_validFor
    ContractInternals.contractBody_invariantFreeOnValid
  intro body
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover marker.span body.span
    value := {
      name
      genericParameters
      bodySpan := body.span
      members := body.members
    }
  } : ContractDecl)

theorem contractDecl_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ declaration next, contractDecl input = .ok declaration next) ∨
      (∃ failure next, contractDecl input = .reject failure next) :=
  contractDecl_invariantFreeOnValid input inputValid

theorem contractDecl_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    contractDecl input ≠ .invariant error :=
  contractDecl_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser
end
