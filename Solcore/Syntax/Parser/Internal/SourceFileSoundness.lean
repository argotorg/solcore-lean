import Solcore.Syntax.Parser.Internal.FileProofs
import Solcore.Syntax.Parser.Internal.ParseProperties
import Solcore.Syntax.Parser.Internal.ContractProofs
import Solcore.Syntax.Internal.SourceFileOutcomes
import Solcore.Syntax.Parser.Internal.OutcomeCompleteness
import Solcore.Syntax.Grammar.SourceFile
import Solcore.Syntax.Parser.Internal.TermSoundness

/-!
Soundness of the parsers of source files: each success and each rejection has its
declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.PublicValidityProperties
/-! Canonical parsed-file validity at the public parser boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Canonical recursive validity for one complete parsed file. -/
abbrev CanonicalParsedFileValid : SourceFile → ParsedFile → Prop :=
  ParsedFile.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor

/-- A successful preflighted parse returns a canonically valid parsed file.

The item-parser laws remain explicit until the outer contract declaration and
derive-aware top-level dispatcher are closed.
-/
theorem parseLexed_ok_parsed_validFor
    (itemValid : FileInternals.parseItemsItem.ValidFor
      FileInternals.RecoveredTopItemValid)
    (itemWindow : Parser.PreservesTokenWindow
      FileInternals.parseItemsItem)
    (file : SourceFile) (lexed : LexedFile) (output : ParseOutput)
    (lexedValid : lexed.ValidFor file)
    (result : parseLexed file lexed = .ok output) :
    CanonicalParsedFileValid file output.parsed := by
  unfold parseLexed at result
  rw [validateLexed_validFor_ok file lexed lexedValid] at result
  change (match checkNesting lexed.tokens with
    | some diagnostic => Except.ok ({
        parsed := {
          source := file.id
          span := SourceSpan.fullFile file
          items := []
          comments := lexed.comments
        }
        tokens := lexed.tokens
        lexicalDiagnostics := lexed.diagnostics
        parseDiagnostics :=
          filterParseDiagnostics file lexed.diagnostics [diagnostic]
      } : ParseOutput)
    | none =>
        match sourceFile lexed.comments (State.initial file lexed) with
        | .ok parsed finalState => Except.ok ({
            parsed
            tokens := lexed.tokens
            lexicalDiagnostics := lexed.diagnostics
            parseDiagnostics := filterParseDiagnostics file
              lexed.diagnostics finalState.diagnostics
          } : ParseOutput)
        | .reject failure _ =>
            Except.error (ParserInvariantError.noProgress
              .topLevel failure.span)
        | .invariant error => Except.error error) = .ok output at result
  cases nesting : checkNesting lexed.tokens with
  | some diagnostic =>
      simp only [nesting] at result
      cases result
      exact ⟨rfl, SourceSpan.fullFile_validFor file, by simp,
        fun _ member => lexedValid.comment_span member⟩
  | none =>
      simp only [nesting] at result
      have initialValid := State.initial_validFor lexedValid
      have parsedReply := FileInternals.sourceFile_reply_validFor itemValid
        itemWindow initialValid
          (fun _ member => lexedValid.comment_span member)
      cases grammar : sourceFile lexed.comments (State.initial file lexed) with
      | ok parsed finalState =>
          rw [grammar] at parsedReply
          simp only [grammar] at result
          cases result
          exact parsedReply.1
      | reject failure rejected =>
          simp only [grammar] at result
          contradiction
      | invariant error =>
          simp only [grammar] at result
          contradiction

/-- Every successful public source parse returns a canonically valid file. -/
theorem parse_ok_parsed_validFor
    (itemValid : FileInternals.parseItemsItem.ValidFor
      FileInternals.RecoveredTopItemValid)
    (itemWindow : Parser.PreservesTokenWindow
      FileInternals.parseItemsItem)
    (file : SourceFile) (output : ParseOutput)
    (result : parse file = .ok output) :
    CanonicalParsedFileValid file output.parsed := by
  unfold parse at result
  cases lexing : Lexer.lex file with
  | error diagnostic => simp [lexing] at result
  | ok lexed =>
      have lexedValid := Lexer.lex_ok_validFor file lexed lexing
      cases parsing : parseLexed file lexed with
      | error error => simp [lexing, parsing] at result
      | ok parsedOutput =>
          have outputEq : parsedOutput = output := by
            simpa [lexing, parsing] using result
          subst output
          exact parseLexed_ok_parsed_validFor itemValid itemWindow file lexed
            parsedOutput lexedValid parsing

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FileCanonicalProperties
/-! Canonical file validity from the completed derive-aware item boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace FileInternals

/-- The derive-aware item contract supplies the canonical predicate expected by
the complete-file loop. -/
theorem parseItemsItem_canonical_validFor (contract : ContractDeclInputs) :
    parseItemsItem.ValidFor RecoveredTopItemValid :=
  (parseItemsItem_contract contract).validFor.mono
    (fun _ _ itemContract => itemContract.validFor)

/-- Complete-file replies retain canonical parsed-file provenance. -/
theorem sourceFile_canonical_reply_validFor
    (contract : ContractDeclInputs) {comments : List Comment} {input : State}
    (inputValid : input.ValidFor)
    (commentsValid : ∀ comment ∈ comments,
      comment.span.ValidFor input.file) :
    (sourceFile comments input).ValidFor input CanonicalParsedFileValid :=
  sourceFile_reply_validFor (parseItemsItem_canonical_validFor contract)
    (parseItemsItem_contract contract).preservesTokenWindow inputValid
    commentsValid

end FileInternals

/-- Preflighted parsing needs only the explicit outer contract-declaration
boundary to return a canonically valid parsed file. -/
theorem parseLexed_ok_canonical_validFor
    (contract : FileInternals.ContractDeclInputs)
    (file : SourceFile) (lexed : LexedFile) (output : ParseOutput)
    (lexedValid : lexed.ValidFor file)
    (result : parseLexed file lexed = .ok output) :
    CanonicalParsedFileValid file output.parsed :=
  parseLexed_ok_parsed_validFor
    (FileInternals.parseItemsItem_canonical_validFor contract)
    (FileInternals.parseItemsItem_contract contract).preservesTokenWindow
    file lexed output lexedValid result

/-- Public source parsing exposes canonical parsed-file validity under the same
single explicit declaration boundary. -/
theorem parse_ok_canonical_validFor
    (contract : FileInternals.ContractDeclInputs)
    (file : SourceFile) (output : ParseOutput)
    (result : parse file = .ok output) :
    CanonicalParsedFileValid file output.parsed :=
  parse_ok_parsed_validFor
    (FileInternals.parseItemsItem_canonical_validFor contract)
    (FileInternals.parseItemsItem_contract contract).preservesTokenWindow
    file output result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FileCompleteProperties
/-! Unconditional canonical contracts for complete-file parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace FileInternals

/-- The completed contract parser discharges the final file-parser input. -/
theorem contractDecl_canonical_inputs : ContractDeclInputs := {
  validFor := contractDecl_canonical_contract.validFor
  preservesTokenWindow := contractDecl_canonical_contract.preservesTokenWindow
  cursorMonotoneOnSuccess :=
    contractDecl_canonical_contract.cursorMonotoneOnSuccess
  startsAtCurrentTokenOnSuccess :=
    contractDecl_canonical_contract.startsAtCurrentTokenOnSuccess
}

theorem parseItemsItem_complete_contract :
    TopItemParserContract parseItemsItem :=
  parseItemsItem_contract contractDecl_canonical_inputs

theorem parseItemsItem_complete_validFor :
    parseItemsItem.ValidFor RecoveredTopItemValid :=
  parseItemsItem_canonical_validFor contractDecl_canonical_inputs

theorem sourceFile_complete_reply_validFor
    {comments : List Comment} {input : State}
    (inputValid : input.ValidFor)
    (commentsValid : ∀ comment ∈ comments,
      comment.span.ValidFor input.file) :
    (sourceFile comments input).ValidFor input CanonicalParsedFileValid :=
  sourceFile_canonical_reply_validFor contractDecl_canonical_inputs
    inputValid commentsValid

theorem parseItems_complete_preservesTokenWindow
    (fuel : Nat) (itemsRev : List TopItem) :
    Parser.PreservesTokenWindow (parseItems fuel itemsRev) :=
  parseItems_canonical_preservesTokenWindow contractDecl_canonical_inputs
    fuel itemsRev

theorem parseItems_complete_preservesTokensOnSuccess
    (fuel : Nat) (itemsRev : List TopItem) :
    Parser.PreservesTokensOnSuccess (parseItems fuel itemsRev) :=
  parseItems_canonical_preservesTokensOnSuccess contractDecl_canonical_inputs
    fuel itemsRev

theorem parseItems_complete_cursorMonotoneOnSuccess
    (fuel : Nat) (itemsRev : List TopItem) :
    Parser.CursorMonotoneOnSuccess (parseItems fuel itemsRev) :=
  parseItems_canonical_cursorMonotoneOnSuccess contractDecl_canonical_inputs
    fuel itemsRev

theorem sourceFile_complete_preservesTokenWindow (comments : List Comment) :
    Parser.PreservesTokenWindow (sourceFile comments) :=
  sourceFile_canonical_preservesTokenWindow contractDecl_canonical_inputs
    comments

theorem sourceFile_complete_preservesTokensOnSuccess
    (comments : List Comment) :
    Parser.PreservesTokensOnSuccess (sourceFile comments) :=
  sourceFile_canonical_preservesTokensOnSuccess contractDecl_canonical_inputs
    comments

theorem sourceFile_complete_cursorMonotoneOnSuccess
    (comments : List Comment) :
    Parser.CursorMonotoneOnSuccess (sourceFile comments) :=
  sourceFile_canonical_cursorMonotoneOnSuccess contractDecl_canonical_inputs
    comments

end FileInternals

theorem parseLexed_ok_complete_validFor
    (file : SourceFile) (lexed : LexedFile) (output : ParseOutput)
    (lexedValid : lexed.ValidFor file)
    (result : parseLexed file lexed = .ok output) :
    CanonicalParsedFileValid file output.parsed :=
  parseLexed_ok_canonical_validFor FileInternals.contractDecl_canonical_inputs
    file lexed output lexedValid result

theorem parse_ok_complete_validFor
    (file : SourceFile) (output : ParseOutput)
    (result : parse file = .ok output) :
    CanonicalParsedFileValid file output.parsed :=
  parse_ok_canonical_validFor FileInternals.contractDecl_canonical_inputs
    file output result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FileRecoveryTotalityProperties
/-! Resource and totality contracts for canonical top-level recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- More fuel than remaining tokens is sufficient for recovery to finish. -/
theorem recoverTopItemAux_exists_ok_of_remainingCount_lt
    (first last : SourceSpan) :
    ∀ fuel state, state.remainingCount < fuel →
      ∃ item final,
        recoverTopItemAux first last fuel state = .ok item final := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      intro state enough
      simp at enough
  | succ fuel inductionHypothesis =>
      intro state enough
      unfold recoverTopItemAux
      split
      · exact ⟨_, _, rfl⟩
      · cases advanced : state.advance? with
        | none => exact ⟨_, _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            change ∃ item final,
              recoverTopItemAux first token.span fuel next = .ok item final
            apply inductionHypothesis
            unfold State.advance? at advanced
            cases found : state.peek? with
            | none => simp [found] at advanced
            | some current =>
                simp only [found, Option.map_some] at advanced
                cases advanced
                have cursorBeforeEnd :=
                  State.cursor_lt_endIndex_of_peek?_eq_some found
                simp only [State.remainingCount] at enough ⊢
                omega

/-- The production fuel selected by `recoverTopItem` always suffices. -/
theorem recoverTopItemAux_production_exists_ok
    (first last : SourceSpan) (state : State) :
    ∃ item final,
      recoverTopItemAux first last (state.remainingCount + 1) state =
        .ok item final :=
  recoverTopItemAux_exists_ok_of_remainingCount_lt first last
    (state.remainingCount + 1) state (by omega)

/-- Recovery has only an ordinary success or rejection, never an invariant. -/
theorem recoverTopItem_ordinary (state : State) :
    (∃ item final, recoverTopItem state = .ok item final) ∨
      (∃ failure final, recoverTopItem state = .reject failure final) := by
  unfold recoverTopItem
  cases advanced : state.advance? with
  | none => exact Or.inr ⟨_, _, rfl⟩
  | some pair =>
      rcases pair with ⟨token, next⟩
      exact Or.inl (recoverTopItemAux_production_exists_ok
        token.span token.span next)

/-- Top-level recovery cannot expose a fuel or progress invariant. -/
theorem recoverTopItem_ne_invariant (state : State)
    (error : ParserInvariantError) :
    recoverTopItem state ≠ .invariant error := by
  intro invariantResult
  rcases recoverTopItem_ordinary state with
    ⟨item, final, result⟩ | ⟨failure, final, result⟩ <;>
      rw [result] at invariantResult <;> contradiction

/-- A valid nonempty recovery window succeeds and strictly consumes input. -/
theorem recoverTopItem_exists_ok_of_validFor_not_atEnd
    (state : State) (stateValid : state.ValidFor)
    (notAtEnd : state.atEnd = false) :
    ∃ item final,
      recoverTopItem state = .ok item final ∧
        state.cursor < final.cursor := by
  have cursorBeforeEnd : state.cursor < state.window.endIndex := by
    simpa [State.atEnd] using notAtEnd
  have cursorBeforeSize : state.cursor < state.tokens.size :=
    Nat.lt_of_lt_of_le cursorBeforeEnd stateValid.endIndex_le_size
  let token := state.tokens[state.cursor]
  have tokenFound : state.tokens[state.cursor]? = some token := by
    exact Array.getElem?_eq_some_iff.mpr ⟨cursorBeforeSize, rfl⟩
  have peekFound : state.peek? = some token := by
    unfold State.peek?
    simp [cursorBeforeEnd, tokenFound]
  have advanced : state.advance? = some
      (token, { state with cursor := state.cursor + 1 }) := by
    simp [State.advance?, peekFound]
  unfold recoverTopItem
  simp only [advanced]
  rcases recoverTopItemAux_production_exists_ok token.span token.span
      { state with cursor := state.cursor + 1 } with
    ⟨item, final, result⟩
  exact ⟨item, final, result,
    recoverTopItem_cursor_lt_onSuccess (by
      unfold recoverTopItem
      simpa only [advanced] using result)⟩

/-- At a window end, recovery reports its ordinary top-item rejection. -/
theorem recoverTopItem_eq_rejectAt_of_atEnd
    (state : State) (atEnd : state.atEnd = true) :
    recoverTopItem state =
      rejectAt state { head := .topItem, tail := [] } .topItem := by
  have cursorAtEnd : state.window.endIndex ≤ state.cursor := by
    simpa [State.atEnd] using atEnd
  have peekNone : state.peek? = none := by
    unfold State.peek?
    simp [Nat.not_lt_of_ge cursorAtEnd]
  unfold recoverTopItem State.advance?
  simp [peekNone]

/-- On valid input, recovery succeeds exactly away from the window end. -/
theorem recoverTopItem_exists_ok_iff_not_atEnd
    (state : State) (stateValid : state.ValidFor) :
    (∃ item final, recoverTopItem state = .ok item final) ↔
      state.atEnd = false := by
  constructor
  · rintro ⟨item, final, recovered⟩
    rcases (recoverTopItem_ok_state_shape recovered).2 with
      ⟨token, tokenFound, _⟩
    have cursorBeforeEnd :=
      State.cursor_lt_endIndex_of_peek?_eq_some tokenFound
    simpa [State.atEnd] using cursorBeforeEnd
  · intro notAtEnd
    rcases recoverTopItem_exists_ok_of_validFor_not_atEnd state stateValid
        notAtEnd with
      ⟨item, final, recovered, _⟩
    exact ⟨item, final, recovered⟩

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TopItemRecoveryOrdinaryOutcomeSoundnessProperties
/-! Exact executable ordinary outcomes for top-item recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

private theorem recoveryAdvance_state_shape {input next : State}
    {token : Token} (advanced : input.advance? = some (token, next)) :
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
theorem recoverTopItemAux_success_ordinaryOutcome_sound
    (first : SourceSpan) :
    ∀ fuel last input item output,
      recoverTopItemAux first last fuel input = .ok item output →
      DeclarativeGrammar.TopItemRecoveryScanParses first last
        input.declarativeRemainder item output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input item output result
      simp [recoverTopItemAux] at result
  | succ fuel inductionHypothesis =>
      intro last input item output result
      unfold recoverTopItemAux at result
      by_cases guard : (input.atEnd || atTopItemStart input) = true
      · simp only [guard, if_true] at result
        unfold finishRecoveredTopItem at result
        cases result
        simpa [State.emit, State.declarativeRemainder,
          DeclarativeGrammar.recoveredTopItemValue] using
          (DeclarativeGrammar.TopItemRecoveryScanParses.stop
            (first := first) (last := last)
            (topItemRecoveryStops_of_guard_eq_true input guard))
      · have guardFalse :
            (input.atEnd || atTopItemStart input) = false :=
          Bool.eq_false_iff.mpr guard
        simp only [guardFalse, Bool.false_eq_true, if_false] at result
        cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredTopItem at result
            cases result
            simpa [State.emit, State.declarativeRemainder,
              DeclarativeGrammar.recoveredTopItemValue] using
              (DeclarativeGrammar.TopItemRecoveryScanParses.stop
                (first := first) (last := last)
                (topItemRecoveryStops_of_advance?_eq_none input guardFalse
                  advanced))
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            rcases recoveryAdvance_state_shape advanced with ⟨found, nextEq⟩
            have tail := inductionHypothesis token.span next item output result
            rw [nextEq] at tail
            exact .next
              (no_topItemRecoveryStops_of_nonBoundary_token guardFalse found)
              (tokenAt_of_peek?_eq_some found) tail

/-- Every executable recovery success consumes its mandatory first token and
then follows the exact boundary-preserving scan. -/
theorem recoverTopItem_success_ordinaryOutcome_sound
    {input output : State} {item : TopItem}
    (result : recoverTopItem input = .ok item output) :
    DeclarativeGrammar.TopItemRecoveryParses
      input.declarativeRemainder item output.declarativeRemainder := by
  unfold recoverTopItem at result
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at result
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases recoveryAdvance_state_shape advanced with ⟨found, nextEq⟩
      have scan := recoverTopItemAux_success_ordinaryOutcome_sound token.span
        (next.remainingCount + 1) token.span next item output result
      rw [nextEq] at scan
      exact .recovered (tokenAt_of_peek?_eq_some found) scan

/-- Every executable recovery rejection exactly records an unavailable
mandatory first token and retains the complete declarative remainder. -/
theorem recoverTopItem_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : recoverTopItem input = .reject failure rejected) :
    DeclarativeGrammar.TopItemRecoveryRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold recoverTopItem at result
  cases advanced : input.advance? with
  | none =>
      simp only [advanced] at result
      unfold rejectAt at result
      cases result
      by_cases atEnd : input.window.endIndex ≤ input.cursor
      · exact .windowEnd atEnd
      · have inside : input.cursor < input.window.endIndex := by omega
        apply DeclarativeGrammar.TopItemRecoveryRejects.missingToken inside
        unfold State.advance? State.peek? at advanced
        simpa [State.declarativeRemainder, inside] using advanced
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases recoverTopItemAux_production_exists_ok token.span token.span next
          with ⟨recovered, output, recoveredResult⟩
      rw [recoveredResult] at result
      contradiction

/-- Package standalone top-item recovery success and rejection. -/
theorem recoverTopItem_ordinaryOutcome_sound :
    (∀ {input output : State} {item : TopItem},
      recoverTopItem input = .ok item output →
        DeclarativeGrammar.TopItemRecoveryParses
          input.declarativeRemainder item output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      recoverTopItem input = .reject failure rejected →
        DeclarativeGrammar.TopItemRecoveryRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨recoverTopItem_success_ordinaryOutcome_sound,
    recoverTopItem_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic standalone recovery outcomes. -/
theorem recoverTopItem_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TopItemRecoveryParses
      DeclarativeGrammar.TopItemRecoveryRejects :=
  DeclarativeGrammar.topItemRecoveryDeterministicOutcomeSpec

/-- Standalone recovery fixes the full error-item AST and both outcome endpoints. -/
theorem recoverTopItem_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemRecoveryParses DeclarativeGrammar.TopItemRecoveryRejects :=
  DeclarativeGrammar.topItemRecoveryExactOutcomeSpec

/-- Recovery successes agree on their complete AST and declarative remainder. -/
theorem recoverTopItem_success_result_unique
    {input leftOutput rightOutput : State} {left right : TopItem}
    (leftResult : recoverTopItem input = .ok left leftOutput)
    (rightResult : recoverTopItem input = .ok right rightOutput) :
    left = right ∧ leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  recoverTopItem_exactOutcomeSpec.successResultUnique
    (recoverTopItem_success_ordinaryOutcome_sound leftResult)
    (recoverTopItem_success_ordinaryOutcome_sound rightResult)

/-- Recovery rejections agree on their original-input declarative endpoint. -/
theorem recoverTopItem_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : recoverTopItem input = .reject leftFailure leftOutput)
    (rightResult : recoverTopItem input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  recoverTopItem_exactOutcomeSpec.rejectOutputUnique
    (recoverTopItem_reject_ordinaryOutcome_sound leftResult)
    (recoverTopItem_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TopItemRecoveryCompletenessProperties
/-! Unconditional complete ordinary grammar correspondence for standalone
top-item recovery, including its mandatory-first-token rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Recovery grammar success is exactly execution with the same recovered
item AST and declarative remainder, without a valid-state premise. -/
theorem recoverTopItem_ordinary_success_iff
    {input : State} {value : TopItem}
    {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TopItemRecoveryParses
      input.declarativeRemainder value remainder ↔
      ∃ output, recoverTopItem input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok recoverTopItem recoverTopItem_exactOutcomeSpec
    (recoverTopItem_ne_invariant input)
    recoverTopItem_success_ordinaryOutcome_sound recoverTopItem_reject_ordinaryOutcome_sound

/-- Recovery grammar rejection is exactly execution at the same declarative
endpoint, without identifying the failure payload or requiring valid input. -/
theorem recoverTopItem_ordinary_reject_iff
    {input : State} {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TopItemRecoveryRejects input.declarativeRemainder rejected ↔
      ∃ failure output, recoverTopItem input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject recoverTopItem recoverTopItem_exactOutcomeSpec
    (recoverTopItem_ne_invariant input)
    recoverTopItem_success_ordinaryOutcome_sound recoverTopItem_reject_ordinaryOutcome_sound

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.SourceFileSoundnessProperties
/-! Parametric diagnostic-free soundness for complete syntax files. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/--
Every diagnostic-free complete-file success follows the strict top-item
grammar and the exact pure comment-attachment transformation.
-/
theorem sourceFile_success_sound
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
    {comments : List Comment} {input next : State}
    {parsedFile : ParsedFile}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : sourceFile comments input = .ok parsedFile next) :
    DeclarativeGrammar.SourceFileParses
      (DeclarativeGrammar.TopItemParses expressionParses allowBodyParses
        requiredBodyParses)
      input.file comments input.declarativeRemainder parsedFile
        next.declarativeRemainder := by
  unfold sourceFile at result
  cases itemsResult : parseItems (input.remainingCount + 1) [] input with
  | invariant error =>
      rw [itemsResult] at result
      cases result
  | reject failure rejected =>
      rw [itemsResult] at result
      cases result
  | ok rawItems afterItems =>
      simp only [itemsResult] at result
      cases result
      rcases parseItems_success_sound_of_diagnosticFree
          (DeclarativeGrammar.TopItemParses expressionParses allowBodyParses
            requiredBodyParses)
          (fun itemFree itemResult =>
            topItem_success_sound expressionParses allowBodyParses
              requiredBodyParses expressionReflects expressionSound
              allowBodyReflects allowBodySound requiredBodyReflects
              requiredBodySound itemFree
                (by simpa only [parseItemsItem] using itemResult))
          (fun itemResult itemFree =>
            topItem_reflectsDiagnosticFreeOnSuccess expressionReflects
              allowBodyReflects requiredBodyReflects _ _ _
                (by simpa only [parseItemsItem] using itemResult) itemFree)
          diagnosticFree itemsResult with
        ⟨suffix, itemsEq, itemsGrammar⟩
      have rawItemsEq : rawItems = suffix := by
        simpa using itemsEq
      subst rawItems
      exact .parsed itemsGrammar

/-- Complete-file grammar soundness composes with canonical source validity. -/
theorem sourceFile_success_sound_and_validFor
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
    {comments : List Comment} {input next : State}
    {parsedFile : ParsedFile} (inputValid : input.ValidFor)
    (commentsValid : ∀ comment ∈ comments,
      comment.span.ValidFor input.file)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : sourceFile comments input = .ok parsedFile next) :
    DeclarativeGrammar.SourceFileParses
        (DeclarativeGrammar.TopItemParses expressionParses allowBodyParses
          requiredBodyParses)
        input.file comments input.declarativeRemainder parsedFile
          next.declarativeRemainder ∧
      ParsedFile.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor input.file
        parsedFile := by
  refine ⟨sourceFile_success_sound expressionParses allowBodyParses
    requiredBodyParses expressionReflects expressionSound allowBodyReflects
    allowBodySound requiredBodyReflects requiredBodySound diagnosticFree result,
    ?_⟩
  have valid := sourceFile_complete_reply_validFor inputValid commentsValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreSourceFileOrdinarySoundnessProperties
/-! Concrete ordinary soundness for complete canonical Core source files. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every diagnostic-free complete-file success follows the concrete ordinary
Core grammar with public expression and isolated-body outcomes. -/
theorem sourceFile_success_coreOrdinary_sound
    {comments : List Comment} {input next : State}
    {parsedFile : ParsedFile}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : sourceFile comments input = .ok parsedFile next) :
    DeclarativeGrammar.CoreSourceFileOrdinaryParses input.file comments
      input.declarativeRemainder parsedFile next.declarativeRemainder := by
  exact sourceFile_success_sound
    DeclarativeGrammar.CoreExpressionOrdinaryParses
    (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
    (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .require)
    expression_reflectsDiagnosticFreeOnSuccess
    (fun _ expressionResult =>
      expression_success_ordinary_sound expressionResult)
    (isolatedPublicCoreBlock_reflectsDiagnosticFreeOnSuccess .allow)
    (fun _ bodyResult =>
      isolatedCoreBlockPublic_success_ordinary_sound .allow bodyResult)
    (isolatedPublicCoreBlock_reflectsDiagnosticFreeOnSuccess .require)
    (fun _ bodyResult =>
      isolatedCoreBlockPublic_success_ordinary_sound .require bodyResult)
    diagnosticFree result

/-- Every valid diagnostic-free complete-file success reaches the canonical
terminal remainder of its preserved token window. -/
theorem sourceFile_success_coreOrdinary_sound_toEnd
    {comments : List Comment} {input next : State}
    {parsedFile : ParsedFile} (inputValid : input.ValidFor)
    (commentsValid : ∀ comment ∈ comments,
      comment.span.ValidFor input.file)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : sourceFile comments input = .ok parsedFile next) :
    DeclarativeGrammar.CoreSourceFileOrdinaryParses input.file comments
      input.declarativeRemainder parsedFile {
        tokens := input.tokens
        endIndex := input.window.endIndex
        cursor := input.window.endIndex
      } := by
  have parsed := sourceFile_success_coreOrdinary_sound diagnosticFree result
  have outputValid := sourceFile_complete_reply_validFor inputValid commentsValid
  rw [result] at outputValid
  have outputShape := sourceFile_complete_preservesTokenWindow comments input
  rw [result] at outputShape
  have cursorEq : next.cursor = input.window.endIndex := by
    apply Nat.le_antisymm
    · simpa [outputShape.2] using outputValid.2.1.cursor_le_endIndex
    · simpa [State.declarativeRemainder, outputShape.2] using
        parsed.output_atEnd
  simpa [State.declarativeRemainder, outputShape.1, outputShape.2, cursorEq]
    using parsed

/-- Concrete complete-file ordinary soundness paired with canonical source
validity. -/
theorem sourceFile_success_coreOrdinary_sound_and_validFor
    {comments : List Comment} {input next : State}
    {parsedFile : ParsedFile} (inputValid : input.ValidFor)
    (commentsValid : ∀ comment ∈ comments,
      comment.span.ValidFor input.file)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : sourceFile comments input = .ok parsedFile next) :
    DeclarativeGrammar.CoreSourceFileOrdinaryParses input.file comments
        input.declarativeRemainder parsedFile next.declarativeRemainder ∧
      ParsedFile.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor input.file
        parsedFile := by
  exact sourceFile_success_sound_and_validFor
    DeclarativeGrammar.CoreExpressionOrdinaryParses
    (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
    (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .require)
    expression_reflectsDiagnosticFreeOnSuccess
    (fun _ expressionResult =>
      expression_success_ordinary_sound expressionResult)
    (isolatedPublicCoreBlock_reflectsDiagnosticFreeOnSuccess .allow)
    (fun _ bodyResult =>
      isolatedCoreBlockPublic_success_ordinary_sound .allow bodyResult)
    (isolatedPublicCoreBlock_reflectsDiagnosticFreeOnSuccess .require)
    (fun _ bodyResult =>
      isolatedCoreBlockPublic_success_ordinary_sound .require bodyResult)
    inputValid commentsValid diagnosticFree result

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.FileItemStrictProperties
/-! Strict cursor progress for complete top-level item parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_cursor_lt_onSuccess_of_first {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    (firstStrict : ∀ {input middle : State} {value : alpha},
      first input = .ok value middle → input.cursor < middle.cursor)
    (nextMonotone : ∀ value, Parser.CursorMonotoneOnSuccess (next value))
    {input final : State} {result : beta}
    (parsed : (first >>= next) input = .ok result final) :
    input.cursor < final.cursor := by
  change (match first input with
    | .ok value middle => next value middle
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok result final at parsed
  cases firstResult : first input with
  | ok value middle =>
      simp only [firstResult] at parsed
      exact Nat.lt_of_lt_of_le (firstStrict firstResult)
        (nextMonotone value middle result final parsed)
  | reject failure rejected => simp [firstResult] at parsed
  | invariant error => simp [firstResult] at parsed

/-- A complete import consumes its leading keyword. -/
theorem importDecl_cursor_lt_onSuccess {input final : State}
    {declaration : ImportDecl}
    (parsed : importDecl input = .ok declaration final) :
    input.cursor < final.cursor := by
  unfold importDecl at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess
      (.keyword .importKw) .importDecl (· == .keyword .importKw) result) ?_ parsed
  intro importKeyword
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases star : isSymbol observed .star
  · simp only [star, if_true]
    by_cases namespaceAlias :
        observed.peekOffsetKind? 1 == some (.keyword .asKw)
    · simp only [namespaceAlias, if_true]
      exact namespaceImport_cursorMonotoneOnSuccess importKeyword.span
    · simp only [namespaceAlias]
      exact wildcardImport_cursorMonotoneOnSuccess importKeyword.span
  · simp only [star]
    by_cases selected : isSymbol observed .leftBrace
    · simp only [selected, if_true]
      exact selectiveImport_cursorMonotoneOnSuccess importKeyword.span
    · simp only [selected]
      exact plainImport_cursorMonotoneOnSuccess importKeyword.span

/-- A complete export consumes its leading keyword. -/
theorem exportDecl_cursor_lt_onSuccess {input final : State}
    {declaration : ExportDecl}
    (parsed : exportDecl input = .ok declaration final) :
    input.cursor < final.cursor := by
  unfold exportDecl at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess
      (.keyword .exportKw) .exportDecl (· == .keyword .exportKw) result) ?_ parsed
  intro exportKeyword
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  split
  · exact localExport_cursorMonotoneOnSuccess exportKeyword.span
  · exact pathExport_cursorMonotoneOnSuccess exportKeyword.span

/-- A complete type alias consumes its leading keyword. -/
theorem typeAlias_cursor_lt_onSuccess {input final : State}
    {declaration : TypeAliasDecl}
    (parsed : typeAlias input = .ok declaration final) :
    input.cursor < final.cursor := by
  unfold typeAlias at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess
      (.keyword .typeKw) .typeAlias (· == .keyword .typeKw) result) ?_ parsed
  intro typeKeyword
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .typeAlias)
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    parseTypeAliasParameters_cursorMonotoneOnSuccess
  intro parameters
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .equal .typeAlias)
  intro equal
  apply Parser.bind_cursorMonotoneOnSuccess
    TypeAliasInternals.parseAliasValue_cursorMonotoneOnSuccess
  intro value
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .typeAlias)
  intro semicolon
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Every complete function consumes its signature's leading keyword. -/
theorem functionDecl_cursor_lt_onSuccess (location : FunctionLocation)
    {input final : State} {declaration : FunctionDecl}
    (parsed : functionDecl location input = .ok declaration final) :
    input.cursor < final.cursor := by
  unfold functionDecl at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (FunctionInternals.functionSignature_cursor_lt_onSuccess location) ?_ parsed
  intro signature
  apply Parser.bind_cursorMonotoneOnSuccess
    (isolateBlock_cursorMonotoneOnSuccess (block .allow)
      (block_canonical_cursorMonotoneOnSuccess .allow))
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Every complete enum consumes its contextual marker. -/
theorem enumDecl_cursor_lt_onSuccess (derive : Option DeriveAttribute)
    {input final : State} {declaration : EnumDecl}
    (parsed : enumDecl derive input = .ok declaration final) :
    input.cursor < final.cursor := by
  unfold enumDecl at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess
      (.contextual .enum) .topItem (·.isContextual .enum) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .topItem)
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    optionalGenericParameters_cursorMonotoneOnSuccess
  intro parameters
  apply Parser.bind_cursorMonotoneOnSuccess
    EnumInternals.enumBody_cursorMonotoneOnSuccess
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

namespace FileInternals

private theorem mapTopItem_cursor_lt_onSuccess {alpha : Type}
    (parser : Parser alpha) (wrap : alpha → TopItem)
    (parserStrict : ∀ {input final : State} {value : alpha},
      parser input = .ok value final → input.cursor < final.cursor)
    {input final : State} {item : TopItem}
    (parsed : mapTopItem parser wrap input = .ok item final) :
    input.cursor < final.cursor := by
  unfold mapTopItem at parsed
  cases result : parser input with
  | invariant error => simp [result] at parsed
  | reject failure rejected => simp [result] at parsed
  | ok value next =>
      simp only [result] at parsed
      cases parsed
      exact parserStrict result

/-- Every successful plain top-level declaration consumes its leading token. -/
theorem plainTopItem_cursor_lt_onSuccess {input final : State} {item : TopItem}
    (parsed : plainTopItem input = .ok item final) :
    input.cursor < final.cursor := by
  unfold plainTopItem at parsed
  split at parsed
  · exact mapTopItem_cursor_lt_onSuccess importDecl wrapImport
      importDecl_cursor_lt_onSuccess parsed
  split at parsed
  · exact mapTopItem_cursor_lt_onSuccess exportDecl wrapExport
      exportDecl_cursor_lt_onSuccess parsed
  split at parsed
  · exact mapTopItem_cursor_lt_onSuccess pragmaDecl wrapPragma
      pragmaDecl_cursor_lt_onSuccess parsed
  split at parsed
  · exact mapTopItem_cursor_lt_onSuccess typeAlias wrapTypeAlias
      typeAlias_cursor_lt_onSuccess parsed
  split at parsed
  · exact mapTopItem_cursor_lt_onSuccess (functionDecl .module) wrapFunction
      (functionDecl_cursor_lt_onSuccess .module) parsed
  split at parsed
  · exact mapTopItem_cursor_lt_onSuccess (enumDecl none) wrapEnum
      (enumDecl_cursor_lt_onSuccess none) parsed
  split at parsed
  · exact mapTopItem_cursor_lt_onSuccess traitDecl wrapTrait
      traitDecl_cursor_lt_onSuccess parsed
  split at parsed
  · exact mapTopItem_cursor_lt_onSuccess implDecl wrapImpl
      implDecl_cursor_lt_onSuccess parsed
  split at parsed
  · exact mapTopItem_cursor_lt_onSuccess contractDecl wrapContract
      contractDecl_canonical_cursor_lt_onSuccess parsed
  · unfold rejectAt at parsed
    contradiction

/-- The derive-aware item boundary always advances on ordinary success. -/
theorem parseItemsItem_cursor_lt_onSuccess {input final : State}
    {item : TopItem} (parsed : parseItemsItem input = .ok item final) :
    input.cursor < final.cursor := by
  unfold parseItemsItem topItem at parsed
  split at parsed
  · cases deriveResult : deriveAttribute input <;> simp [deriveResult] at parsed
    rename_i derive afterDerive
    cases itemResult : plainTopItem afterDerive <;> simp [itemResult] at parsed
    rename_i inner next
    exact Nat.lt_of_lt_of_le (deriveAttribute_cursor_lt_onSuccess deriveResult)
      (Nat.le_trans
        ((plainTopItem_contract contractDecl_canonical_inputs
          ).cursorMonotoneOnSuccess
          afterDerive inner next itemResult)
        (attachDeriveAttribute_cursorMonotoneOnSuccess derive inner
          next item final parsed))
  · exact plainTopItem_cursor_lt_onSuccess parsed

end FileInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FileItemsOutcomePrimitiveProperties
/-! Shared executable primitives for broad source-file item-loop outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- A complete top-item rejection and its canonical state contract supply the
declarative rewind witness used by the file loop. -/
theorem topItemRejectsWithPreservedWindow_of_result
    {input failed : State} {failure : Failure}
    (result : parseItemsItem input = .reject failure failed) :
    DeclarativeGrammar.TopItemRejectsWithPreservedWindow
      input.declarativeRemainder := by
  have resultShape := parseItemsItem_complete_contract.preservesTokenWindow input
  rw [result] at resultShape
  have shape : failed.tokens = input.tokens ∧
      failed.window = input.window := by
    simpa only [Reply.PreservesTokenWindow] using resultShape
  exact ⟨failed.declarativeRemainder,
    topItem_reject_ordinaryOutcome_sound
      (by simpa only [parseItemsItem] using result),
    shape.1, congrArg TokenWindow.endIndex shape.2⟩

/-- Preserved carrier and active window make the file-loop cursor rewind
declaratively invisible. -/
theorem rewoundTopItem_declarativeRemainder_eq
    (input failed : State)
    (shape : failed.tokens = input.tokens ∧ failed.window = input.window) :
    ({ failed with cursor := input.cursor } : State).declarativeRemainder =
      input.declarativeRemainder := by
  unfold State.declarativeRemainder
  simp only
  rw [shape.1, shape.2]

/-- A false executable end guard is exactly strict containment in the active
token window. -/
theorem fileItemsCursor_lt_endIndex_of_atEnd_eq_false {input : State}
    (notAtEnd : input.atEnd = false) :
    input.cursor < input.window.endIndex := by
  unfold State.atEnd at notAtEnd
  have outside : ¬ input.window.endIndex ≤ input.cursor := by
    intro atEnd
    rw [decide_eq_true atEnd] at notAtEnd
    contradiction
  omega

/-- A true executable boundary guard exposes the exact top-item boundary. -/
theorem fileItemsBoundaryStartsAt_of_guard_eq_true {input : State}
    (present : atTopItemStart input = true) :
    DeclarativeGrammar.ImportTerminatorTopItemStartsAt
      input.declarativeRemainder :=
  importTerminatorTopItemStartsAt_of_atTopItemStart_eq_true present

/-- A false executable boundary guard excludes every exact top-item
boundary. -/
theorem no_fileItemsBoundaryStartsAt_of_guard_eq_false {input : State}
    (absent : atTopItemStart input = false) :
    ¬ DeclarativeGrammar.ImportTerminatorTopItemStartsAt
      input.declarativeRemainder := by
  intro starts
  have present := atTopItemStart_eq_true_of_topItemRecoveryBoundary starts
  rw [present] at absent
  contradiction

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.FileItemsOrdinaryRejectionSoundnessProperties
/-! Broad ordinary-rejection soundness for source-file item accumulation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every rejecting fuel-bounded file-item loop records the exact first
rejection of its prioritized end, item, rewind, boundary, recovery, and
recursive branches. -/
theorem parseItems_reject_ordinaryOutcome_sound :
    ∀ fuel itemsRev input failure rejected,
      parseItems fuel itemsRev input = .reject failure rejected →
      DeclarativeGrammar.FileItemsRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input failure rejected result
      simp [parseItems] at result
  | succ fuel inductionHypothesis =>
      intro itemsRev input failure rejected result
      unfold parseItems at result
      cases ended : input.atEnd with
      | true => simp [ended] at result
      | false =>
          simp only [ended, Bool.false_eq_true, if_false] at result
          have inside := fileItemsCursor_lt_endIndex_of_atEnd_eq_false ended
          cases itemResult : parseItemsItem input with
          | invariant error => simp [itemResult] at result
          | ok item afterItem =>
              simp only [itemResult] at result
              by_cases progress : afterItem.cursor > input.cursor
              · simp only [progress, if_true] at result
                exact .laterDirect inside
                  (topItem_ordinaryOutcome_sound.1
                    (by simpa only [parseItemsItem] using itemResult))
                  progress
                  (inductionHypothesis (item :: itemsRev) afterItem failure
                    rejected result)
              · simp [progress] at result
          | reject itemFailure failedState =>
              simp only [itemResult] at result
              have itemRejected :=
                topItemRejectsWithPreservedWindow_of_result itemResult
              have resultShape :=
                parseItemsItem_complete_contract.preservesTokenWindow input
              rw [itemResult] at resultShape
              have shape : failedState.tokens = input.tokens ∧
                  failedState.window = input.window := by
                simpa only [Reply.PreservesTokenWindow] using resultShape
              let rewound : State := {
                failedState with cursor := input.cursor
              }
              have rewoundEq : rewound.declarativeRemainder =
                  input.declarativeRemainder := by
                dsimp only [rewound]
                exact rewoundTopItem_declarativeRemainder_eq input failedState
                  shape
              change (if atTopItemStart input then
                    .ok itemsRev.reverse (rewound.emit itemFailure.toDiagnostic)
                  else match recoverTopItem rewound with
                    | .ok recovered afterRecovery =>
                        parseItems fuel (recovered :: itemsRev) afterRecovery
                    | .reject recoveryFailure recoveryRejected =>
                        .reject recoveryFailure recoveryRejected
                    | .invariant error => .invariant error) =
                .reject failure rejected at result
              cases boundary : atTopItemStart input with
              | true => simp [boundary] at result
              | false =>
                  simp only [boundary, Bool.false_eq_true, if_false] at result
                  have boundaryAbsent :=
                    no_fileItemsBoundaryStartsAt_of_guard_eq_false boundary
                  cases recoveryResult : recoverTopItem rewound with
                  | invariant error => simp [recoveryResult] at result
                  | reject recoveryFailure recoveryRejected =>
                      simp only [recoveryResult] at result
                      cases result
                      have recoveryGrammar :=
                        recoverTopItem_reject_ordinaryOutcome_sound
                          recoveryResult
                      rw [rewoundEq] at recoveryGrammar
                      exact .recoveryRejected inside itemRejected boundaryAbsent
                        recoveryGrammar
                  | ok recovered afterRecovery =>
                      simp only [recoveryResult] at result
                      have recoveryGrammar :=
                        recoverTopItem_success_ordinaryOutcome_sound
                          recoveryResult
                      rw [rewoundEq] at recoveryGrammar
                      exact .laterRecovered inside itemRejected boundaryAbsent
                        recoveryGrammar
                        (inductionHypothesis (recovered :: itemsRev)
                          afterRecovery failure rejected result)

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.FileItemsOrdinarySuccessSoundnessProperties
/-! Broad ordinary-success reflection for the source-file item loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every successful fuel-bounded file-item loop exposes the forward suffix
added after its executable reverse accumulator and its exact broad outcome. -/
theorem parseItems_success_ordinaryOutcome_sound_strong :
    ∀ fuel itemsRev input items output,
      parseItems fuel itemsRev input = .ok items output →
      ∃ suffix,
        items = itemsRev.reverse ++ suffix ∧
        DeclarativeGrammar.FileItemsOrdinaryParses
          input.declarativeRemainder suffix output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input items output result
      simp [parseItems] at result
  | succ fuel inductionHypothesis =>
      intro itemsRev input items output result
      unfold parseItems at result
      cases ended : input.atEnd with
      | true =>
          simp only [ended, if_true] at result
          cases result
          refine ⟨[], by simp, .done ?_⟩
          simpa [State.atEnd, State.declarativeRemainder] using ended
      | false =>
          simp only [ended, Bool.false_eq_true, if_false] at result
          have inside := fileItemsCursor_lt_endIndex_of_atEnd_eq_false ended
          cases itemResult : parseItemsItem input with
          | invariant error => simp [itemResult] at result
          | ok item afterItem =>
              simp only [itemResult] at result
              by_cases progress : afterItem.cursor > input.cursor
              · simp only [progress, if_true] at result
                rcases inductionHypothesis (item :: itemsRev) afterItem items
                    output result with
                  ⟨suffix, itemsEq, tailParsed⟩
                have itemParsed := topItem_success_ordinaryOutcome_sound
                  (by simpa only [parseItemsItem] using itemResult)
                have declarativeProgress :
                    input.declarativeRemainder.cursor <
                      afterItem.declarativeRemainder.cursor := by
                  simpa [State.declarativeRemainder] using progress
                refine ⟨item :: suffix, ?_, .direct inside itemParsed
                  declarativeProgress tailParsed⟩
                · simpa [List.reverse_cons, List.append_assoc] using itemsEq
              · simp only [progress, if_false] at result
                contradiction
          | reject failure failedState =>
              simp only [itemResult] at result
              have itemRejected :=
                topItemRejectsWithPreservedWindow_of_result itemResult
              have resultShape :=
                parseItemsItem_complete_contract.preservesTokenWindow input
              rw [itemResult] at resultShape
              have shape : failedState.tokens = input.tokens ∧
                  failedState.window = input.window := by
                simpa only [Reply.PreservesTokenWindow] using resultShape
              let rewound : State := {
                failedState with cursor := input.cursor
              }
              have rewoundEq : rewound.declarativeRemainder =
                  input.declarativeRemainder := by
                dsimp only [rewound]
                exact rewoundTopItem_declarativeRemainder_eq input failedState
                  shape
              change (if atTopItemStart input then
                  .ok itemsRev.reverse (rewound.emit failure.toDiagnostic)
                else match recoverTopItem rewound with
                  | .ok recovered next =>
                      parseItems fuel (recovered :: itemsRev) next
                  | .reject recoveryFailure rejected =>
                      .reject recoveryFailure rejected
                  | .invariant error => .invariant error) =
                .ok items output at result
              cases boundary : atTopItemStart input with
              | true =>
                  simp only [boundary, if_true] at result
                  cases result
                  refine ⟨[], by simp, ?_⟩
                  have outputEq :
                      (rewound.emit failure.toDiagnostic).declarativeRemainder =
                        input.declarativeRemainder := by
                    simpa [State.emit, State.declarativeRemainder] using
                      rewoundEq
                  rw [outputEq]
                  exact .boundaryStop inside itemRejected
                    (fileItemsBoundaryStartsAt_of_guard_eq_true boundary)
              | false =>
                  simp only [boundary, Bool.false_eq_true, if_false] at result
                  cases recoveryResult : recoverTopItem rewound with
                  | invariant error => simp [recoveryResult] at result
                  | reject recoveryFailure rejected =>
                      simp [recoveryResult] at result
                  | ok recovered afterRecovery =>
                      simp only [recoveryResult] at result
                      rcases inductionHypothesis (recovered :: itemsRev)
                          afterRecovery items output result with
                        ⟨suffix, itemsEq, tailParsed⟩
                      have recoveryParsed :=
                        recoverTopItem_success_ordinaryOutcome_sound
                          recoveryResult
                      rw [rewoundEq] at recoveryParsed
                      refine ⟨recovered :: suffix, ?_,
                        .recovered inside itemRejected
                          (no_fileItemsBoundaryStartsAt_of_guard_eq_false
                            boundary)
                          recoveryParsed tailParsed⟩
                      simpa [List.reverse_cons, List.append_assoc]
                        using itemsEq

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.FileItemsOrdinaryOutcomeSoundnessProperties
/-! Complete broad executable outcomes for source-file item accumulation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Package exact executable success and rejection for any fuel and reverse
accumulator, keeping the latter outside the declarative grammar. -/
theorem parseItems_ordinaryOutcome_sound (fuel : Nat)
    (itemsRev : List TopItem) :
    (∀ {input output : State} {items : List TopItem},
      parseItems fuel itemsRev input = .ok items output →
        ∃ suffix,
          items = itemsRev.reverse ++ suffix ∧
          DeclarativeGrammar.FileItemsOrdinaryParses
            input.declarativeRemainder suffix output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      parseItems fuel itemsRev input = .reject failure rejected →
        DeclarativeGrammar.FileItemsRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨fun {input output items} result =>
      parseItems_success_ordinaryOutcome_sound_strong fuel itemsRev input
        items output result,
    fun {input rejected failure} result =>
      parseItems_reject_ordinaryOutcome_sound fuel itemsRev input failure
        rejected result⟩

/-- Re-export deterministic and exclusive broad file-item outcomes. -/
theorem parseItems_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.FileItemsOrdinaryParses
      DeclarativeGrammar.FileItemsRejects :=
  DeclarativeGrammar.fileItemsDeterministicOutcomeSpec

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.SourceFileOrdinaryOutcomeSoundnessProperties
/-! Complete broad executable outcomes for canonical syntax files. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every executable complete-file success follows the recovery-aware item
grammar and exact pure comment-attachment transformation. -/
theorem sourceFile_success_ordinaryOutcome_sound
    {comments : List Comment} {input output : State}
    {parsedFile : ParsedFile}
    (result : sourceFile comments input = .ok parsedFile output) :
    DeclarativeGrammar.SourceFileOrdinaryParses input.file comments
      input.declarativeRemainder parsedFile output.declarativeRemainder := by
  unfold sourceFile at result
  split at result
  next reply rawItems afterItems itemsResult =>
      cases result
      rcases parseItems_success_ordinaryOutcome_sound_strong
          (input.remainingCount + 1) [] input rawItems output itemsResult
          with ⟨suffix, itemsEq, itemsParsed⟩
      have rawItemsEq : rawItems = suffix := by simpa using itemsEq
      subst rawItems
      exact .parsed itemsParsed
  next => contradiction
  next => contradiction

/-- Every executable complete-file rejection is exactly the item loop's first
ordinary rejection. -/
theorem sourceFile_reject_ordinaryOutcome_sound
    {comments : List Comment} {input rejected : State} {failure : Failure}
    (result : sourceFile comments input = .reject failure rejected) :
    DeclarativeGrammar.SourceFileRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold sourceFile at result
  split at result
  next => contradiction
  next reply itemsFailure itemsRejected itemsResult =>
      cases result
      exact .itemsRejected
        (parseItems_reject_ordinaryOutcome_sound
          (input.remainingCount + 1) [] input failure rejected itemsResult)
  next => contradiction

/-- Package unconditional executable success and rejection for complete syntax
files. -/
theorem sourceFile_ordinaryOutcome_sound (comments : List Comment) :
    (∀ {input output : State} {parsedFile : ParsedFile},
      sourceFile comments input = .ok parsedFile output →
        DeclarativeGrammar.SourceFileOrdinaryParses input.file comments
          input.declarativeRemainder parsedFile output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      sourceFile comments input = .reject failure rejected →
        DeclarativeGrammar.SourceFileRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨sourceFile_success_ordinaryOutcome_sound,
    sourceFile_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad complete-file outcomes. -/
theorem sourceFile_ordinaryOutcomeSpec
    (file : SourceFile) (comments : List Comment) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.SourceFileOrdinaryParses file comments)
      DeclarativeGrammar.SourceFileRejects :=
  DeclarativeGrammar.sourceFileDeterministicOutcomeSpec file comments

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.FileItemsExactnessProperties
/-! Exact executable file-item results without exposing the reverse accumulator. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Successful top-item values supply the exact declarative file-loop contract. -/
theorem parseItems_exactOutcomeSpec_of_topItemValues
    (itemValues : ∀ {input left right afterLeft afterRight},
      DeclarativeGrammar.TopItemOrdinaryParses input left afterLeft →
      DeclarativeGrammar.TopItemOrdinaryParses input right afterRight → left = right) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FileItemsOrdinaryParses DeclarativeGrammar.FileItemsRejects :=
  DeclarativeGrammar.fileItemsExactOutcomeSpecOfTopItemValues itemValues

/-- An exact top-item contract supplies exact declarative file-loop outcomes. -/
theorem parseItems_exactOutcomeSpec_of_topItem
    (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FileItemsOrdinaryParses DeclarativeGrammar.FileItemsRejects :=
  DeclarativeGrammar.fileItemsExactOutcomeSpecOfTopItem itemOutcomes

/-- At fixed fuel and reverse accumulator, executable item loops agree on the
complete forward result and remainder from unique top-item success values. -/
theorem parseItems_success_result_unique_of_topItemValues
    (itemValues : ∀ {input left right afterLeft afterRight},
      DeclarativeGrammar.TopItemOrdinaryParses input left afterLeft →
      DeclarativeGrammar.TopItemOrdinaryParses input right afterRight → left = right)
    (fuel : Nat) (itemsRev : List TopItem)
    {input leftOutput rightOutput : State} {left right : List TopItem}
    (leftResult : parseItems fuel itemsRev input = .ok left leftOutput)
    (rightResult : parseItems fuel itemsRev input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder := by
  rcases parseItems_success_ordinaryOutcome_sound_strong fuel itemsRev input
      left leftOutput leftResult with ⟨leftSuffix, leftEq, leftParsed⟩
  rcases parseItems_success_ordinaryOutcome_sound_strong fuel itemsRev input
      right rightOutput rightResult with ⟨rightSuffix, rightEq, rightParsed⟩
  rcases (parseItems_exactOutcomeSpec_of_topItemValues itemValues)
      |>.successResultUnique leftParsed rightParsed with ⟨suffixEq, outputEq⟩
  constructor
  · rw [leftEq, rightEq, suffixEq]
  · exact outputEq

/-- Exact top-item outcomes fix an executable item loop's result and remainder. -/
theorem parseItems_success_result_unique_of_topItem
    (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    (fuel : Nat) (itemsRev : List TopItem)
    {input leftOutput rightOutput : State} {left right : List TopItem}
    (leftResult : parseItems fuel itemsRev input = .ok left leftOutput)
    (rightResult : parseItems fuel itemsRev input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  parseItems_success_result_unique_of_topItemValues itemOutcomes.successValueUnique
    fuel itemsRev leftResult rightResult

/-- Executable file-item rejection endpoints agree unconditionally. -/
theorem parseItems_reject_output_unique
    (fuel : Nat) (itemsRev : List TopItem)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : parseItems fuel itemsRev input = .reject leftFailure leftOutput)
    (rightResult : parseItems fuel itemsRev input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.FileItemsRejects.output_unique
    (parseItems_reject_ordinaryOutcome_sound fuel itemsRev input
      leftFailure leftOutput leftResult)
    (parseItems_reject_ordinaryOutcome_sound fuel itemsRev input
      rightFailure rightOutput rightResult)

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.SourceFileExactnessProperties
/-! Exact executable source-file values and rejection endpoints. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Successful top-item values supply exact files at fixed provenance and comments. -/
theorem sourceFile_exactOutcomeSpec_of_topItemValues
    (itemValues : ∀ {input left right afterLeft afterRight},
      DeclarativeGrammar.TopItemOrdinaryParses input left afterLeft →
      DeclarativeGrammar.TopItemOrdinaryParses input right afterRight → left = right)
    (file : SourceFile) (comments : List Comment) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.SourceFileOrdinaryParses file comments)
      DeclarativeGrammar.SourceFileRejects :=
  DeclarativeGrammar.sourceFileExactOutcomeSpecOfTopItemValues itemValues file comments

/-- An exact top-item contract supplies exact complete source-file outcomes. -/
theorem sourceFile_exactOutcomeSpec_of_topItem
    (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    (file : SourceFile) (comments : List Comment) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.SourceFileOrdinaryParses file comments)
      DeclarativeGrammar.SourceFileRejects :=
  DeclarativeGrammar.sourceFileExactOutcomeSpecOfTopItem itemOutcomes file comments

/-- With the same supplied comments and input state, source-file successes
agree on their full attached AST and remainder. -/
theorem sourceFile_success_result_unique_of_topItemValues
    (itemValues : ∀ {input left right afterLeft afterRight},
      DeclarativeGrammar.TopItemOrdinaryParses input left afterLeft →
      DeclarativeGrammar.TopItemOrdinaryParses input right afterRight → left = right)
    (comments : List Comment)
    {input leftOutput rightOutput : State} {left right : ParsedFile}
    (leftResult : sourceFile comments input = .ok left leftOutput)
    (rightResult : sourceFile comments input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (sourceFile_exactOutcomeSpec_of_topItemValues itemValues input.file comments)
    |>.successResultUnique
      (sourceFile_success_ordinaryOutcome_sound leftResult)
      (sourceFile_success_ordinaryOutcome_sound rightResult)

/-- Exact top-item outcomes fix successful source-file ASTs and remainders. -/
theorem sourceFile_success_result_unique_of_topItem
    (itemOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemOrdinaryParses DeclarativeGrammar.TopItemRejects)
    (comments : List Comment)
    {input leftOutput rightOutput : State} {left right : ParsedFile}
    (leftResult : sourceFile comments input = .ok left leftOutput)
    (rightResult : sourceFile comments input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  sourceFile_success_result_unique_of_topItemValues itemOutcomes.successValueUnique
    comments leftResult rightResult

/-- Executable source-file rejection endpoints agree without top-item exactness. -/
theorem sourceFile_reject_output_unique (comments : List Comment)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : sourceFile comments input = .reject leftFailure leftOutput)
    (rightResult : sourceFile comments input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.SourceFileRejects.output_unique
    (sourceFile_reject_ordinaryOutcome_sound leftResult)
    (sourceFile_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PublicDiagnosticValidityProperties
/-! Parse-diagnostic provenance at the public parser boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every parse diagnostic returned after preflight points into the input file. -/
theorem parseLexed_ok_parseDiagnostics_validFor
    (contract : FileInternals.ContractDeclInputs)
    (file : SourceFile) (lexed : LexedFile) (output : ParseOutput)
    (result : parseLexed file lexed = .ok output) :
    ∀ diagnostic ∈ output.parseDiagnostics,
      diagnostic.span.ValidFor file := by
  have lexedValid := parseLexed_ok_input_validFor file lexed output result
  unfold parseLexed at result
  rw [validateLexed_validFor_ok file lexed lexedValid] at result
  change (match checkNesting lexed.tokens with
    | some diagnostic => Except.ok ({
        parsed := {
          source := file.id
          span := SourceSpan.fullFile file
          items := []
          comments := lexed.comments
        }
        tokens := lexed.tokens
        lexicalDiagnostics := lexed.diagnostics
        parseDiagnostics :=
          filterParseDiagnostics file lexed.diagnostics [diagnostic]
      } : ParseOutput)
    | none =>
        match sourceFile lexed.comments (State.initial file lexed) with
        | .ok parsed finalState => Except.ok ({
            parsed
            tokens := lexed.tokens
            lexicalDiagnostics := lexed.diagnostics
            parseDiagnostics := filterParseDiagnostics file
              lexed.diagnostics finalState.diagnostics
          } : ParseOutput)
        | .reject failure _ =>
            Except.error (ParserInvariantError.noProgress
              .topLevel failure.span)
        | .invariant error => Except.error error) = .ok output at result
  cases nesting : checkNesting lexed.tokens with
  | some nestingDiagnostic =>
      have nestingValid := checkNesting_lexed_some_span_validFor file lexed
        lexedValid nesting
      simp only [nesting] at result
      cases result
      exact filterParseDiagnostics_spans_validFor file lexed.diagnostics
        [nestingDiagnostic] (by
          intro diagnostic member
          simp only [List.mem_singleton] at member
          cases member
          exact nestingValid)
  | none =>
      simp only [nesting] at result
      have initialValid := State.initial_validFor lexedValid
      have grammarReply := FileInternals.sourceFile_canonical_reply_validFor
        contract initialValid (fun _ member => lexedValid.comment_span member)
      cases grammar : sourceFile lexed.comments (State.initial file lexed) with
      | ok parsed finalState =>
          rw [grammar] at grammarReply
          simp only [grammar] at result
          cases result
          apply filterParseDiagnostics_spans_validFor
          intro diagnostic member
          have validInFinal :=
            grammarReply.2.1.diagnostics_span_validFor member
          simpa [State.initial, grammarReply.2.2] using validInFinal
      | reject failure rejected =>
          simp only [grammar] at result
          contradiction
      | invariant error =>
          simp only [grammar] at result
          contradiction

/-- Every parse diagnostic returned by public source parsing is source-valid. -/
theorem parse_ok_parseDiagnostics_validFor
    (contract : FileInternals.ContractDeclInputs)
    (file : SourceFile) (output : ParseOutput)
    (result : parse file = .ok output) :
    ∀ diagnostic ∈ output.parseDiagnostics,
      diagnostic.span.ValidFor file := by
  unfold parse at result
  cases lexing : Lexer.lex file with
  | error diagnostic => simp [lexing] at result
  | ok lexed =>
      cases parsing : parseLexed file lexed with
      | error error => simp [lexing, parsing] at result
      | ok parsedOutput =>
          have outputEq : parsedOutput = output := by
            simpa [lexing, parsing] using result
          subst output
          exact parseLexed_ok_parseDiagnostics_validFor contract file lexed
            parsedOutput parsing

end Solcore.Syntax.Parser
end
