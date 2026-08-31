import Solcore.Syntax.Parser.FunctionProperties
import Solcore.Syntax.Parser.Trait
import Solcore.Syntax.CallableDeclarationValidity

/-! Ordinary-result contracts for canonical trait parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem traitBind_ok_components {α β : Type} {first : Parser α}
    {next : α → Parser β} {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst, first input = .ok firstValue afterFirst ∧
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

namespace TraitInternals

namespace TraitBody

/-- Every trait-body range and retained method belongs to one source. -/
def ValidFor (file : SourceFile) (body : TraitBody) : Prop :=
  body.span.ValidFor file ∧
    List.ValidFor TraitMethod.ValidFor file body.methods

end TraitBody

/-- A signature-only trait method retains only ranges from its source. -/
theorem traitMethod_validFor :
    traitMethod.ValidFor TraitMethod.ValidFor := by
  intro input inputValid
  have weak : traitMethod.ValidFor (fun _ _ => True) := by
    unfold traitMethod
    apply Parser.bind_validFor (functionSignature_validFor .module)
    intro signature
    apply Parser.bind_validFor (symbol_validFor .semicolon .topItem)
    intro semicolon
    exact Parser.pure_validFor _ _ (fun _ => trivial)
  have weakResult := weak input inputValid
  cases parsed : traitMethod input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok method final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold traitMethod at stages
      rcases traitBind_ok_components stages with
        ⟨signature, afterSignature, signatureResult, rest⟩
      rcases traitBind_ok_components rest with
        ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
      have signatureReply := functionSignature_validFor .module input inputValid
      rw [signatureResult] at signatureReply
      have semicolonReply := symbol_validFor .semicolon .topItem
        afterSignature signatureReply.2.1
      rw [semicolonResult] at semicolonReply
      have signatureValid : FunctionSignature.ValidFor input.file signature := by
        simpa [signatureReply.2.2] using signatureReply.1
      have semicolonValid : semicolon.span.ValidFor input.file := by
        simpa only [Located.ValidFor, semicolonReply.2.2,
          signatureReply.2.2] using semicolonReply.1
      rcases functionSignature_startsAtCurrentTokenOnSuccess .module
          input signature afterSignature signatureResult with
        ⟨first, firstFound, signatureStart⟩
      have firstAt := State.getElem?_eq_some_of_peek?_eq_some firstFound
      have semicolonShape := symbol_ok_state_shape .semicolon .topItem
        semicolonResult
      have signatureTokens := functionSignature_preservesTokensOnSuccess .module
        input signature afterSignature signatureResult
      have semicolonAt : input.tokens[afterSignature.cursor]? = some semicolon := by
        simpa [signatureTokens] using
          State.getElem?_eq_some_of_peek?_eq_some semicolonShape.1
      have separated := inputValid.token_end_le_token_start_of_getElem?_lt
        firstAt semicolonAt
          (FunctionInternals.functionSignature_cursor_lt_onSuccess .module
            signatureResult)
      have firstValid := inputValid.peek?_span_validFor firstFound
      have ordered : signature.span.startByte ≤ semicolon.span.endByte := by
        calc
          signature.span.startByte = first.span.startByte := signatureStart.symm
          _ ≤ first.span.endByte := firstValid.2.1
          _ ≤ semicolon.span.startByte := separated
          _ ≤ semicolon.span.endByte := semicolonValid.2.1
      have outerValid := SourceSpan.cover_validFor signatureValid.1
        semicolonValid ordered
      cases finished
      exact ⟨⟨outerValid, by simp, signatureValid, semicolonValid⟩,
        weakResult.2.1, weakResult.2.2⟩

/-- Trait methods retain the signature parser's ordinary token window. -/
theorem traitMethod_preservesTokenWindow
    (signatureShape : Parser.PreservesTokenWindow
      (functionSignature .module)) :
    Parser.PreservesTokenWindow traitMethod := by
  unfold traitMethod
  apply Parser.bind_preservesTokenWindow signatureShape
  intro signature
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .semicolon .topItem)
  intro semicolon
  exact Parser.pure_preservesTokenWindow _

/-- Closing a trait body retains its braces and accumulated methods. -/
private theorem closeTraitBody_validFor (opening : Token)
    (methodsRev : List TraitMethod) (input : State) (openingIndex : Nat)
    (inputValid : input.ValidFor)
    (openingFound : input.tokens[openingIndex]? = some opening)
    (openingBefore : openingIndex < input.cursor)
    (methodsValid : List.ValidFor TraitMethod.ValidFor
      input.file methodsRev) :
    (closeTraitBody opening methodsRev input).ValidFor input
      TraitBody.ValidFor := by
  unfold closeTraitBody
  have closingReply := symbol_validFor .rightBrace .topItem input inputValid
  cases closingResult : symbol .rightBrace .topItem input with
  | invariant error =>
      simp only [bind, closingResult]
      trivial
  | reject failure rejected =>
      rw [closingResult] at closingReply
      simp only [bind, closingResult]
      exact closingReply
  | ok closing next =>
      rw [closingResult] at closingReply
      simp only [bind, closingResult, pure, Reply.ValidFor]
      have closingShape := symbol_ok_state_shape .rightBrace .topItem
        closingResult
      have closingAt := State.getElem?_eq_some_of_peek?_eq_some closingShape.1
      have openingValid :=
        inputValid.token_span_validFor_of_getElem?_eq_some openingFound
      have closingValid : closing.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using closingReply.1
      have separated := inputValid.token_end_le_token_start_of_getElem?_lt
        openingFound closingAt openingBefore
      have ordered : opening.span.startByte ≤ closing.span.endByte :=
        Nat.le_trans openingValid.2.1
          (Nat.le_trans separated closingValid.2.1)
      refine ⟨⟨SourceSpan.cover_validFor openingValid closingValid ordered, ?_⟩,
        closingReply.2.1, closingReply.2.2⟩
      intro method member
      exact methodsValid method (by simpa using member)

/-- The fuel-bounded trait loop retains every parsed method and body range. -/
theorem traitMethods_validFor (opening : Token) :
    ∀ fuel methodsRev input openingIndex,
      input.ValidFor →
      input.tokens[openingIndex]? = some opening →
      openingIndex < input.cursor →
      List.ValidFor TraitMethod.ValidFor input.file methodsRev →
      (traitMethods opening fuel methodsRev input).ValidFor input
        TraitBody.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro methodsRev input openingIndex inputValid openingFound
        openingBefore methodsValid
      unfold traitMethods
      split
      · exact closeTraitBody_validFor opening methodsRev input openingIndex
          inputValid openingFound openingBefore methodsValid
      · split
        · have methodReply := traitMethod_validFor input inputValid
          cases methodResult : traitMethod input with
          | invariant error => trivial
          | reject failure rejected =>
              rw [methodResult] at methodReply
              exact methodReply
          | ok method next =>
              rw [methodResult] at methodReply
              simp only
              split
              · have methodTokens := traitMethod_preservesTokenWindow
                  (functionSignature_preservesTokenWindow .module)
                  |>.preservesTokensOnSuccess
                have openingFoundNext : next.tokens[openingIndex]? =
                    some opening := by
                  simpa [methodTokens input method next methodResult] using
                    openingFound
                have accumulated : List.ValidFor TraitMethod.ValidFor
                    next.file (method :: methodsRev) := by
                  intro retained member
                  simp only [List.mem_cons] at member
                  rcases member with retainedEq | retainedMember
                  · subst retained
                    simpa [methodReply.2.2] using methodReply.1
                  · simpa [methodReply.2.2] using
                      methodsValid retained retainedMember
                have progress : input.cursor < next.cursor := by omega
                exact (inductionHypothesis (method :: methodsRev) next
                  openingIndex methodReply.2.1 openingFoundNext
                    (Nat.lt_trans openingBefore progress) accumulated
                      ).of_file_eq methodReply.2.2
              · trivial
        · unfold rejectAt Reply.ValidFor
          exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩

/-- A complete trait body retains both braces and every method. -/
theorem traitBody_validFor : traitBody.ValidFor TraitBody.ValidFor := by
  intro input inputValid
  unfold traitBody
  have openingReply := symbol_validFor .leftBrace .topItem input inputValid
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [openingResult] at openingReply
      exact openingReply
  | ok opening next =>
      rw [openingResult] at openingReply
      have openingShape := symbol_ok_state_shape .leftBrace .topItem
        openingResult
      have openingAtInput :=
        State.getElem?_eq_some_of_peek?_eq_some openingShape.1
      have openingAtNext : next.tokens[input.cursor]? = some opening := by
        simpa [openingShape.2] using openingAtInput
      exact (traitMethods_validFor opening (next.remainingCount + 1) [] next
        input.cursor openingReply.2.1 openingAtNext (by simp [openingShape.2])
          (by simp [List.ValidFor])).of_file_eq openingReply.2.2

private theorem closeTraitBody_preservesTokenWindow (opening : Token)
    (methodsRev : List TraitMethod) :
    Parser.PreservesTokenWindow (closeTraitBody opening methodsRev) := by
  unfold closeTraitBody
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .rightBrace .topItem)
  intro closing
  exact Parser.pure_preservesTokenWindow _

/-- The fuel-bounded trait-method loop preserves ordinary token windows. -/
theorem traitMethods_preservesTokenWindow
    (signatureShape : Parser.PreservesTokenWindow
      (functionSignature .module)) (opening : Token) :
    ∀ fuel methodsRev,
      Parser.PreservesTokenWindow (traitMethods opening fuel methodsRev) := by
  intro fuel
  induction fuel with
  | zero => intro methodsRev input; trivial
  | succ fuel inductionHypothesis =>
      intro methodsRev input
      unfold traitMethods
      split
      · exact closeTraitBody_preservesTokenWindow opening methodsRev input
      · split
        · have methodShape :=
            traitMethod_preservesTokenWindow signatureShape input
          cases methodResult : traitMethod input with
          | ok method next =>
              rw [methodResult] at methodShape
              change (if next.cursor > input.cursor then
                traitMethods opening fuel (method :: methodsRev) next
                else .invariant (.noProgress .topLevel next.currentSpan)
                ).PreservesTokenWindow input
              split
              · exact (inductionHypothesis (method :: methodsRev) next).trans
                  methodShape
              · trivial
          | reject failure rejected =>
              rw [methodResult] at methodShape
              exact methodShape
          | invariant error => trivial
        · exact rejectAt_preservesTokenWindow input _ _

/-- Trait bodies preserve every ordinary token window. -/
theorem traitBody_preservesTokenWindow
    (signatureShape : Parser.PreservesTokenWindow
      (functionSignature .module)) :
    Parser.PreservesTokenWindow traitBody := by
  intro input
  unfold traitBody
  have openingShape := symbol_preservesTokenWindow .leftBrace .topItem input
  cases openingResult : symbol .leftBrace .topItem input with
  | ok opening next =>
      rw [openingResult] at openingShape
      exact (traitMethods_preservesTokenWindow signatureShape opening
        (next.remainingCount + 1) [] next).trans openingShape
  | reject failure rejected =>
      rw [openingResult] at openingShape
      exact openingShape
  | invariant error => trivial

private theorem closeTraitBody_cursorMonotoneOnSuccess (opening : Token)
    (methodsRev : List TraitMethod) :
    Parser.CursorMonotoneOnSuccess (closeTraitBody opening methodsRev) := by
  unfold closeTraitBody
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightBrace .topItem)
  intro closing
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- The fuel-bounded trait-method loop never rewinds on success. -/
theorem traitMethods_cursorMonotoneOnSuccess (opening : Token) :
    ∀ fuel methodsRev,
      Parser.CursorMonotoneOnSuccess (traitMethods opening fuel methodsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro methodsRev input body next result
      unfold traitMethods at result
      contradiction
  | succ fuel inductionHypothesis =>
      intro methodsRev input body next result
      unfold traitMethods at result
      split at result
      · exact closeTraitBody_cursorMonotoneOnSuccess opening methodsRev
          input body next result
      · split at result
        · cases methodResult : traitMethod input with
          | ok method afterMethod =>
              simp only [methodResult] at result
              split at result
              · exact Nat.le_trans (Nat.le_of_lt (by assumption))
                  (inductionHypothesis (method :: methodsRev) afterMethod
                    body next result)
              · contradiction
          | reject failure rejected => simp [methodResult] at result
          | invariant error => simp [methodResult] at result
        · unfold rejectAt at result
          contradiction

/-- Successful trait-body parsing never rewinds its caller. -/
theorem traitBody_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess traitBody := by
  intro input body final result
  unfold traitBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | ok opening next =>
      simp only [openingResult] at result
      exact Nat.le_trans
        (symbol_cursorMonotoneOnSuccess .leftBrace .topItem input opening next
          openingResult)
        (traitMethods_cursorMonotoneOnSuccess opening
          (next.remainingCount + 1) [] next body final result)
  | reject failure rejected => simp [openingResult] at result
  | invariant error => simp [openingResult] at result

end TraitInternals

/-- Complete trait declarations preserve ordinary token windows. -/
theorem traitDecl_preservesTokenWindow
    (signatureShape : Parser.PreservesTokenWindow
      (functionSignature .module))
    (whereShape : Parser.PreservesTokenWindow whereClause) :
    Parser.PreservesTokenWindow traitDecl := by
  unfold traitDecl
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .trait .topItem)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .topItem)
  intro name
  apply Parser.bind_preservesTokenWindow genericParameters_preservesTokenWindow
  intro genericParameters
  apply Parser.bind_preservesTokenWindow whereShape
  intro whereClause
  apply Parser.bind_preservesTokenWindow
    (TraitInternals.traitBody_preservesTokenWindow signatureShape)
  intro body
  exact Parser.pure_preservesTokenWindow _

theorem traitDecl_preservesTokensOnSuccess
    (signatureShape : Parser.PreservesTokenWindow
      (functionSignature .module))
    (whereShape : Parser.PreservesTokenWindow whereClause) :
    Parser.PreservesTokensOnSuccess traitDecl :=
  (traitDecl_preservesTokenWindow signatureShape whereShape
    ).preservesTokensOnSuccess

/-- Complete trait declarations never rewind their caller. -/
theorem traitDecl_cursorMonotoneOnSuccess
    (whereMonotone : Parser.CursorMonotoneOnSuccess whereClause) :
    Parser.CursorMonotoneOnSuccess traitDecl := by
  unfold traitDecl
  apply Parser.bind_cursorMonotoneOnSuccess
    (contextual_cursorMonotoneOnSuccess .trait .topItem)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .topItem)
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    genericParameters_cursorMonotoneOnSuccess
  intro genericParameters
  apply Parser.bind_cursorMonotoneOnSuccess whereMonotone
  intro whereClause
  apply Parser.bind_cursorMonotoneOnSuccess
    TraitInternals.traitBody_cursorMonotoneOnSuccess
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful trait declaration starts at its current `trait` token. -/
theorem traitDecl_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess traitDecl (·.span) := by
  unfold traitDecl
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (contextual_startsAtCurrentTokenOnSuccess .trait .topItem)
  intro marker input declaration final parsed
  rcases traitBind_ok_components parsed with
    ⟨name, afterName, _nameResult, rest⟩
  rcases traitBind_ok_components rest with
    ⟨genericParameters, afterParameters, _parametersResult, rest⟩
  rcases traitBind_ok_components rest with
    ⟨whereClause, afterWhere, _whereResult, rest⟩
  rcases traitBind_ok_components rest with
    ⟨body, afterBody, _bodyResult, finished⟩
  cases finished
  rfl

end Solcore.Syntax.Parser
