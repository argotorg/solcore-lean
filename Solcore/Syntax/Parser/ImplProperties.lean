import Solcore.Syntax.Parser.Impl
import Solcore.Syntax.Parser.FunctionProperties
import Solcore.Syntax.CallableDeclarationValidity

/-! State-shape contracts for canonical implementation parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ImplInternals

/-- Requiring nonempty head arguments leaves the token window unchanged. -/
theorem requireImplArguments_preservesTokenWindow
    (values : DelimitedList TypeExpr) :
    Parser.PreservesTokenWindow (requireImplArguments values) := by
  intro input
  unfold requireImplArguments
  cases values.elements <;> trivial

/-- Requiring nonempty head arguments never rewinds on success. -/
theorem requireImplArguments_cursorMonotoneOnSuccess
    (values : DelimitedList TypeExpr) :
    Parser.CursorMonotoneOnSuccess (requireImplArguments values) := by
  intro input result next parsed
  unfold requireImplArguments at parsed
  cases elements : values.elements with
  | nil => simp [elements] at parsed
  | cons head tail => simp [elements] at parsed; cases parsed; exact Nat.le_refl _

/-- An implementation method preserves windows when function bodies do. -/
theorem implMethod_preservesTokenWindow_of_block
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    Parser.PreservesTokenWindow implMethod := by
  unfold implMethod
  apply Parser.bind_preservesTokenWindow
    (functionDecl_preservesTokenWindow_of_block .module bodyWindow)
  intro declaration
  exact Parser.pure_preservesTokenWindow _

private theorem closeImplBody_preservesTokenWindow (opening : Token)
    (methodsRev : List ImplMethod) :
    Parser.PreservesTokenWindow (closeImplBody opening methodsRev) := by
  unfold closeImplBody
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .rightBrace .topItem)
  intro closing
  exact Parser.pure_preservesTokenWindow _

/-- The fuel-bounded method loop preserves every ordinary token window. -/
theorem implMethods_preservesTokenWindow_of_block
    (bodyWindow : Parser.PreservesTokenWindow (block .allow))
    (opening : Token) : ∀ fuel methodsRev,
    Parser.PreservesTokenWindow (implMethods opening fuel methodsRev) := by
  intro fuel
  induction fuel with
  | zero => intro methodsRev input; trivial
  | succ fuel inductionHypothesis =>
      intro methodsRev input
      unfold implMethods
      split
      · exact closeImplBody_preservesTokenWindow opening methodsRev input
      · split
        · have methodShape :=
            implMethod_preservesTokenWindow_of_block bodyWindow input
          cases methodResult : implMethod input with
          | ok method next =>
              rw [methodResult] at methodShape
              change (if next.cursor > input.cursor then
                implMethods opening fuel (method :: methodsRev) next
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

/-- Implementation bodies preserve windows when nested function bodies do. -/
theorem implBody_preservesTokenWindow_of_block
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    Parser.PreservesTokenWindow implBody := by
  intro input
  unfold implBody
  have openingShape := symbol_preservesTokenWindow .leftBrace .topItem input
  cases openingResult : symbol .leftBrace .topItem input with
  | ok opening next =>
      rw [openingResult] at openingShape
      exact (implMethods_preservesTokenWindow_of_block bodyWindow opening
        (next.remainingCount + 1) [] next).trans openingShape
  | reject failure rejected => rw [openingResult] at openingShape; exact openingShape
  | invariant error => trivial

private theorem closeImplBody_cursorMonotoneOnSuccess (opening : Token)
    (methodsRev : List ImplMethod) :
    Parser.CursorMonotoneOnSuccess (closeImplBody opening methodsRev) := by
  unfold closeImplBody
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightBrace .topItem)
  intro closing
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- The method loop's explicit progress guard makes success monotone. -/
theorem implMethods_cursorMonotoneOnSuccess (opening : Token) :
    ∀ fuel methodsRev,
      Parser.CursorMonotoneOnSuccess (implMethods opening fuel methodsRev) := by
  intro fuel
  induction fuel with
  | zero => intro methodsRev input body next parsed; contradiction
  | succ fuel inductionHypothesis =>
      intro methodsRev input body next parsed
      unfold implMethods at parsed
      split at parsed
      · exact closeImplBody_cursorMonotoneOnSuccess opening methodsRev
          input body next parsed
      · split at parsed
        · cases methodResult : implMethod input with
          | ok method afterMethod =>
              simp only [methodResult] at parsed
              split at parsed
              · exact Nat.le_trans (Nat.le_of_lt (by assumption))
                  (inductionHypothesis (method :: methodsRev) afterMethod
                    body next parsed)
              · contradiction
          | reject failure rejected => simp [methodResult] at parsed
          | invariant error => simp [methodResult] at parsed
        · unfold rejectAt at parsed
          contradiction

/-- Successful implementation-body parsing never rewinds its caller. -/
theorem implBody_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess implBody := by
  intro input body final parsed
  unfold implBody at parsed
  cases openingResult : symbol .leftBrace .topItem input with
  | ok opening next =>
      simp only [openingResult] at parsed
      exact Nat.le_trans
        (symbol_cursorMonotoneOnSuccess .leftBrace .topItem input opening next
          openingResult)
        (implMethods_cursorMonotoneOnSuccess opening
          (next.remainingCount + 1) [] next body final parsed)
  | reject failure rejected => simp [openingResult] at parsed
  | invariant error => simp [openingResult] at parsed

end ImplInternals

private theorem implBind_ok_components {α β : Type} {first : Parser α}
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

namespace ImplInternals

/-- Optional `default` parsing preserves every ordinary token window. -/
theorem implDefaultMarker_preservesTokenWindow :
    Parser.PreservesTokenWindow implDefaultMarker := by
  unfold implDefaultMarker
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (keyword_preservesTokenWindow .defaultKw .topItem)
    intro marker
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

theorem implDefaultMarker_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess implDefaultMarker :=
  implDefaultMarker_preservesTokenWindow.preservesTokensOnSuccess

/-- The declaration suffix preserves windows when nested function bodies do. -/
theorem implDeclAfterDefault_preservesTokenWindow_of_block
    (defaultMarker : Option SourceSpan)
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    Parser.PreservesTokenWindow (implDeclAfterDefault defaultMarker) := by
  unfold implDeclAfterDefault
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .impl .topItem)
  intro marker
  apply Parser.bind_preservesTokenWindow optionalGenericParameters_preservesTokenWindow
  intro genericParameters
  apply Parser.bind_preservesTokenWindow (identifier_preservesTokenWindow .topItem)
  intro traitName
  apply Parser.bind_preservesTokenWindow
    (delimited_preservesTokenWindow .less .greater false typeExpr
      .typeExpr .topLevel typeExpr_preservesTokenWindow)
  intro arguments
  apply Parser.bind_preservesTokenWindow
    (requireImplArguments_preservesTokenWindow arguments)
  intro headArguments
  apply Parser.bind_preservesTokenWindow whereClause_preservesTokenWindow
  intro whereClause
  apply Parser.bind_preservesTokenWindow
    (implBody_preservesTokenWindow_of_block bodyWindow)
  intro body
  exact Parser.pure_preservesTokenWindow _

theorem implDeclAfterDefault_preservesTokensOnSuccess_of_block
    (defaultMarker : Option SourceSpan)
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    Parser.PreservesTokensOnSuccess (implDeclAfterDefault defaultMarker) :=
  (implDeclAfterDefault_preservesTokenWindow_of_block defaultMarker
    bodyWindow).preservesTokensOnSuccess

/-- Optional `default` parsing never rewinds its caller. -/
theorem implDefaultMarker_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess implDefaultMarker := by
  unfold implDefaultMarker
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (keyword_cursorMonotoneOnSuccess .defaultKw .topItem)
    intro marker
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- A retained default marker starts at the caller's current token. -/
theorem implDefaultMarker_some_startsAtCurrentTokenOnSuccess
    {input final : State} {marker : SourceSpan}
    (parsed : implDefaultMarker input = .ok (some marker) final) :
    ∃ token, input.peek? = some token ∧
      token.span.startByte = marker.startByte := by
  unfold implDefaultMarker getState at parsed
  simp only [bind] at parsed
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at parsed
    cases tokenResult : keyword .defaultKw .topItem input with
    | invariant error => simp [tokenResult] at parsed
    | reject failure rejected => simp [tokenResult] at parsed
    | ok defaultToken next =>
        simp only [tokenResult] at parsed
        have starts := acceptToken_startsAtCurrentTokenOnSuccess
          (.keyword .defaultKw) .topItem (· == .keyword .defaultKw)
          input defaultToken next tokenResult
        cases parsed
        exact starts
  · simp only [present, Bool.false_eq_true, if_false] at parsed
    change Reply.ok none input = Reply.ok (some marker) final at parsed
    cases parsed

/-- Every successful suffix consumes at least its contextual `impl` token. -/
theorem implDeclAfterDefault_cursor_lt_onSuccess
    (defaultMarker : Option SourceSpan) {input final : State}
    {declaration : ImplDecl}
    (parsed : implDeclAfterDefault defaultMarker input =
      .ok declaration final) : input.cursor < final.cursor := by
  unfold implDeclAfterDefault at parsed
  rcases implBind_ok_components parsed with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases implBind_ok_components rest with
    ⟨genericParameters, afterGenerics, genericsResult, rest⟩
  rcases implBind_ok_components rest with
    ⟨traitName, afterName, nameResult, rest⟩
  rcases implBind_ok_components rest with
    ⟨arguments, afterArguments, argumentsResult, rest⟩
  rcases implBind_ok_components rest with
    ⟨headArguments, afterHead, headResult, rest⟩
  rcases implBind_ok_components rest with
    ⟨whereClause, afterWhere, whereResult, rest⟩
  rcases implBind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact Nat.lt_of_lt_of_le
    (acceptToken_cursor_lt_onSuccess (.contextual .impl) .topItem
      (·.isContextual .impl) markerResult)
    (Nat.le_trans
      (optionalGenericParameters_cursorMonotoneOnSuccess afterMarker
        genericParameters afterGenerics genericsResult)
      (Nat.le_trans (identifier_cursorMonotoneOnSuccess .topItem
          afterGenerics traitName afterName nameResult)
        (Nat.le_trans (delimited_cursorMonotoneOnSuccess .less .greater false
            typeExpr .typeExpr .topLevel afterName arguments afterArguments
            argumentsResult)
          (Nat.le_trans (requireImplArguments_cursorMonotoneOnSuccess arguments
              afterArguments headArguments afterHead headResult)
            (Nat.le_trans (whereClause_cursorMonotoneOnSuccess afterHead
                whereClause afterWhere whereResult)
              (implBody_cursorMonotoneOnSuccess afterWhere body final
                bodyResult))))))

theorem implDeclAfterDefault_cursorMonotoneOnSuccess
    (defaultMarker : Option SourceSpan) :
    Parser.CursorMonotoneOnSuccess (implDeclAfterDefault defaultMarker) := by
  intro input declaration final parsed
  exact Nat.le_of_lt (implDeclAfterDefault_cursor_lt_onSuccess defaultMarker parsed)

end ImplInternals

open ImplInternals

/-- Complete implementation parsing preserves ordinary token windows. -/
theorem implDecl_preservesTokenWindow_of_block
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    Parser.PreservesTokenWindow implDecl := by
  unfold implDecl
  apply Parser.bind_preservesTokenWindow implDefaultMarker_preservesTokenWindow
  intro defaultMarker
  exact implDeclAfterDefault_preservesTokenWindow_of_block defaultMarker bodyWindow

/-- Successful implementation parsing retains the immutable token carrier. -/
theorem implDecl_preservesTokensOnSuccess_of_block
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    Parser.PreservesTokensOnSuccess implDecl :=
  (implDecl_preservesTokenWindow_of_block bodyWindow).preservesTokensOnSuccess

/-- Every successful implementation consumes at least its `impl` marker. -/
theorem implDecl_cursor_lt_onSuccess {input final : State}
    {declaration : ImplDecl} (parsed : implDecl input = .ok declaration final) :
    input.cursor < final.cursor := by
  unfold implDecl at parsed
  rcases implBind_ok_components parsed with
    ⟨defaultMarker, afterDefault, defaultResult, declarationResult⟩
  exact Nat.lt_of_le_of_lt
    (implDefaultMarker_cursorMonotoneOnSuccess input defaultMarker
      afterDefault defaultResult)
    (implDeclAfterDefault_cursor_lt_onSuccess defaultMarker declarationResult)

/-- Complete implementation parsing never rewinds on success. -/
theorem implDecl_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess implDecl := by
  intro input declaration final parsed
  exact Nat.le_of_lt (implDecl_cursor_lt_onSuccess parsed)

/-- A suffix retains its contextual marker or the supplied earlier prefix. -/
theorem ImplInternals.implDeclAfterDefault_startOnSuccess
    (defaultMarker : Option SourceSpan) {input final : State}
    {declaration : ImplDecl}
    (parsed : implDeclAfterDefault defaultMarker input =
      .ok declaration final) :
    ∃ marker afterMarker,
      contextual .impl .topItem input = .ok marker afterMarker ∧
      declaration.span.startByte =
        (defaultMarker.getD marker.span).startByte := by
  unfold implDeclAfterDefault at parsed
  rcases implBind_ok_components parsed with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases implBind_ok_components rest with ⟨generics, afterGenerics, _, rest⟩
  rcases implBind_ok_components rest with ⟨traitName, afterName, _, rest⟩
  rcases implBind_ok_components rest with ⟨arguments, afterArguments, _, rest⟩
  rcases implBind_ok_components rest with ⟨headArguments, afterHead, _, rest⟩
  rcases implBind_ok_components rest with ⟨whereClause, afterWhere, _, rest⟩
  rcases implBind_ok_components rest with ⟨body, afterBody, _, finished⟩
  cases finished
  exact ⟨marker, afterMarker, markerResult, rfl⟩

/-- A complete implementation starts at `default`, when present, or `impl`. -/
theorem implDecl_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess implDecl (·.span) := by
  intro input declaration final parsed
  unfold implDecl at parsed
  rcases implBind_ok_components parsed with
    ⟨defaultMarker, afterDefault, defaultResult, declarationResult⟩
  rcases implDeclAfterDefault_startOnSuccess defaultMarker declarationResult with
    ⟨marker, afterMarker, markerResult, declarationStart⟩
  unfold implDefaultMarker getState at defaultResult
  simp only [bind] at defaultResult
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at defaultResult
    cases tokenResult : keyword .defaultKw .topItem input with
    | invariant error => simp [tokenResult] at defaultResult
    | reject failure rejected => simp [tokenResult] at defaultResult
    | ok defaultToken next =>
        simp only [tokenResult] at defaultResult
        have starts := acceptToken_startsAtCurrentTokenOnSuccess
          (.keyword .defaultKw) .topItem (· == .keyword .defaultKw)
          input defaultToken next tokenResult
        cases defaultResult
        rcases starts with ⟨token, found, start⟩
        exact ⟨token, found, by simpa [declarationStart] using start⟩
  · simp only [present, Bool.false_eq_true, if_false] at defaultResult
    cases defaultResult
    rcases contextual_startsAtCurrentTokenOnSuccess .impl .topItem
        input marker afterMarker markerResult with ⟨token, found, start⟩
    exact ⟨token, found, by simpa [declarationStart] using start⟩

namespace ImplInternals

namespace ImplBody

/-- Every implementation-body range and retained method belongs to one source. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (body : ImplBody) : Prop :=
  body.span.ValidFor file ∧
    List.ValidFor (ImplMethod.ValidFor statementValid) file body.methods

end ImplBody

/-- Requiring nonempty head arguments preserves recursive type provenance. -/
theorem requireImplArguments_reply_validFor
    (values : DelimitedList TypeExpr) (input : State)
    (inputValid : input.ValidFor)
    (valuesValid : values.ValidFor TypeExpr.ValidFor input.file) :
    (requireImplArguments values input).ValidFor input
      (NonemptyDelimitedList.ValidFor TypeExpr.ValidFor) := by
  unfold requireImplArguments
  cases elements : values.elements with
  | nil => trivial
  | cons head tail =>
      simp only [Reply.ValidFor, NonemptyDelimitedList.ValidFor]
      refine ⟨⟨valuesValid.1, ?_⟩, inputValid, rfl⟩
      intro element member
      apply valuesValid.2 element
      simpa [NonemptyList.toList, elements] using member

/-- One implementation method retains its function and empty comment prefix. -/
theorem implMethod_validFor (statementValid : SourceFile → Statement → Prop)
    (blockValid : (block .allow).ValidFor
      (Block.ValidFor statementValid)) :
    implMethod.ValidFor (ImplMethod.ValidFor statementValid) := by
  unfold implMethod
  apply Parser.bind_validFor_of_value
    (functionDecl_validFor statementValid .module blockValid)
  intro declaration input inputValid declarationValid
  exact ⟨⟨declarationValid.1, by simp, declarationValid⟩,
    inputValid, rfl⟩

private theorem closeImplBody_validFor
    (statementValid : SourceFile → Statement → Prop) (opening : Token)
    (methodsRev : List ImplMethod) (input : State) (openingIndex : Nat)
    (inputValid : input.ValidFor)
    (openingFound : input.tokens[openingIndex]? = some opening)
    (openingBefore : openingIndex < input.cursor)
    (methodsValid : List.ValidFor (ImplMethod.ValidFor statementValid)
      input.file methodsRev) :
    (closeImplBody opening methodsRev input).ValidFor input
      (ImplBody.ValidFor statementValid) := by
  unfold closeImplBody
  have closingReply := symbol_validFor .rightBrace .topItem input inputValid
  cases closingResult : symbol .rightBrace .topItem input with
  | invariant error => simp only [bind, closingResult]; trivial
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

/-- The method loop retains every method and the complete body range. -/
theorem implMethods_validFor
    (statementValid : SourceFile → Statement → Prop)
    (blockValid : (block .allow).ValidFor (Block.ValidFor statementValid))
    (bodyWindow : Parser.PreservesTokenWindow (block .allow))
    (opening : Token) : ∀ fuel methodsRev input openingIndex,
      input.ValidFor → input.tokens[openingIndex]? = some opening →
      openingIndex < input.cursor →
      List.ValidFor (ImplMethod.ValidFor statementValid) input.file methodsRev →
      (implMethods opening fuel methodsRev input).ValidFor input
        (ImplBody.ValidFor statementValid) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro methodsRev input openingIndex inputValid openingFound
        openingBefore methodsValid
      unfold implMethods
      split
      · exact closeImplBody_validFor statementValid opening methodsRev input
          openingIndex inputValid openingFound openingBefore methodsValid
      · split
        · have methodReply := implMethod_validFor statementValid blockValid
            input inputValid
          cases methodResult : implMethod input with
          | invariant error => trivial
          | reject failure rejected =>
              rw [methodResult] at methodReply
              exact methodReply
          | ok method next =>
              rw [methodResult] at methodReply
              simp only
              split
              · have methodTokens :=
                  (implMethod_preservesTokenWindow_of_block bodyWindow
                    ).preservesTokensOnSuccess
                have openingFoundNext : next.tokens[openingIndex]? =
                    some opening := by
                  simpa [methodTokens input method next methodResult] using
                    openingFound
                have accumulated : List.ValidFor
                    (ImplMethod.ValidFor statementValid) next.file
                    (method :: methodsRev) := by
                  intro retained member
                  rcases List.mem_cons.mp member with rfl | retainedMember
                  · simpa [methodReply.2.2] using methodReply.1
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

/-- A complete implementation body retains both braces and every method. -/
theorem implBody_validFor
    (statementValid : SourceFile → Statement → Prop)
    (blockValid : (block .allow).ValidFor (Block.ValidFor statementValid))
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    implBody.ValidFor (ImplBody.ValidFor statementValid) := by
  intro input inputValid
  unfold implBody
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
      exact (implMethods_validFor statementValid blockValid bodyWindow opening
        (next.remainingCount + 1) [] next input.cursor openingReply.2.1
        openingAtNext (by simp [openingShape.2])
        (by simp [List.ValidFor])).of_file_eq openingReply.2.2

private theorem implMethods_preservesOpeningStartOnSuccess
    (opening : Token) : ∀ fuel methodsRev input body final,
    implMethods opening fuel methodsRev input = .ok body final →
      body.span.startByte = opening.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro methodsRev input body final parsed
      unfold implMethods at parsed
      split at parsed
      · unfold closeImplBody at parsed
        rcases implBind_ok_components parsed with
          ⟨closing, afterClosing, closingResult, finished⟩
        cases finished
        rfl
      · split at parsed
        · cases methodResult : implMethod input with
          | invariant error => simp [methodResult] at parsed
          | reject failure rejected => simp [methodResult] at parsed
          | ok method next =>
              simp only [methodResult] at parsed
              split at parsed
              · exact inductionHypothesis (method :: methodsRev) next body
                  final parsed
              · contradiction
        · simp [rejectAt] at parsed

/-- A complete implementation body starts at its opening brace token. -/
theorem implBody_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess implBody (·.span) := by
  intro input body final parsed
  unfold implBody at parsed
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok opening next =>
      simp only [openingResult] at parsed
      have openingShape := symbol_ok_state_shape .leftBrace .topItem
        openingResult
      have retained := implMethods_preservesOpeningStartOnSuccess opening
        (next.remainingCount + 1) [] next body final parsed
      exact ⟨opening, openingShape.1, retained.symm⟩

/-- Optional default parsing retains only a valid marker when present. -/
theorem implDefaultMarker_validFor :
    implDefaultMarker.ValidFor
      (Option.ValidFor (fun file span => span.ValidFor file)) := by
  unfold implDefaultMarker
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_validFor_of_value
      (keyword_validFor .defaultKw .topItem)
    intro marker input inputValid markerValid
    exact ⟨by simpa only [Option.ValidFor, Located.ValidFor] using markerValid,
      inputValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)

end ImplInternals

/-- Complete implementation declarations retain only source-valid syntax. -/
theorem implDecl_validFor
    (statementValid : SourceFile → Statement → Prop)
    (blockValid : (block .allow).ValidFor
      (Block.ValidFor statementValid))
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    implDecl.ValidFor (ImplDecl.ValidFor statementValid) := by
  intro input inputValid
  have weak : implDecl.ValidFor (fun _ _ => True) := by
    unfold implDecl
    apply Parser.bind_validFor ImplInternals.implDefaultMarker_validFor
    intro defaultMarker
    unfold ImplInternals.implDeclAfterDefault
    apply Parser.bind_validFor (contextual_validFor .impl .topItem)
    intro marker
    apply Parser.bind_validFor optionalGenericParameters_validFor
    intro genericParameters
    apply Parser.bind_validFor (identifier_validFor .topItem)
    intro traitName
    apply Parser.bind_validFor
      (delimited_validFor TypeExpr.ValidFor .less .greater false typeExpr
        .typeExpr .topLevel typeExpr_validFor
        typeExpr_preservesTokensOnSuccess)
    intro arguments
    have requireWeak : (ImplInternals.requireImplArguments arguments).ValidFor
        (fun _ _ => True) := by
      intro state stateValid
      unfold ImplInternals.requireImplArguments
      cases arguments.elements with
      | nil => trivial
      | cons head tail => exact ⟨trivial, stateValid, rfl⟩
    apply Parser.bind_validFor requireWeak
    intro headArguments
    apply Parser.bind_validFor whereClause_validFor
    intro parsedWhereClause
    apply Parser.bind_validFor
      (ImplInternals.implBody_validFor statementValid blockValid bodyWindow)
    intro body
    exact Parser.pure_validFor _ _ (fun _ => trivial)
  have weakResult := weak input inputValid
  cases parsed : implDecl input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok declaration final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold implDecl at stages
      rcases implBind_ok_components stages with
        ⟨defaultMarker, afterDefault, defaultResult, suffix⟩
      unfold ImplInternals.implDeclAfterDefault at suffix
      rcases implBind_ok_components suffix with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases implBind_ok_components rest with
        ⟨genericParameters, afterGenerics, genericsResult, rest⟩
      rcases implBind_ok_components rest with
        ⟨traitName, afterName, nameResult, rest⟩
      rcases implBind_ok_components rest with
        ⟨arguments, afterArguments, argumentsResult, rest⟩
      rcases implBind_ok_components rest with
        ⟨headArguments, afterHead, headResult, rest⟩
      rcases implBind_ok_components rest with
        ⟨parsedWhereClause, afterWhere, whereResult, rest⟩
      rcases implBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have defaultReply := ImplInternals.implDefaultMarker_validFor input
        inputValid
      rw [defaultResult] at defaultReply
      have markerReply := contextual_validFor .impl .topItem afterDefault
        defaultReply.2.1
      rw [markerResult] at markerReply
      have genericsReply := optionalGenericParameters_validFor afterMarker
        markerReply.2.1
      rw [genericsResult] at genericsReply
      have nameReply := identifier_validFor .topItem afterGenerics
        genericsReply.2.1
      rw [nameResult] at nameReply
      have argumentsReply := delimited_validFor TypeExpr.ValidFor .less
        .greater false typeExpr .typeExpr .topLevel typeExpr_validFor
        typeExpr_preservesTokensOnSuccess afterName nameReply.2.1
      rw [argumentsResult] at argumentsReply
      have argumentsValidAfter : DelimitedList.ValidFor TypeExpr.ValidFor
          afterArguments.file arguments := by
        simpa [argumentsReply.2.2] using argumentsReply.1
      have headReply := ImplInternals.requireImplArguments_reply_validFor
        arguments afterArguments argumentsReply.2.1 argumentsValidAfter
      rw [headResult] at headReply
      have whereReply := whereClause_validFor afterHead headReply.2.1
      rw [whereResult] at whereReply
      have bodyReply := ImplInternals.implBody_validFor statementValid
        blockValid bodyWindow afterWhere whereReply.2.1
      rw [bodyResult] at bodyReply
      have defaultValid : Option.ValidFor
          (fun file span => span.ValidFor file) input.file defaultMarker := by
        exact defaultReply.1
      have markerValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor, defaultReply.2.2] using markerReply.1
      have genericsValid : Option.ValidFor
          (NonemptyDelimitedList.ValidFor Located.ValidFor) input.file
          genericParameters := by
        simpa [markerReply.2.2, defaultReply.2.2] using genericsReply.1
      have nameValid : traitName.span.ValidFor input.file := by
        simpa only [Located.ValidFor, genericsReply.2.2,
          markerReply.2.2, defaultReply.2.2] using nameReply.1
      have headValid : NonemptyDelimitedList.ValidFor TypeExpr.ValidFor
          input.file headArguments := by
        simpa [headReply.2.2, argumentsReply.2.2, nameReply.2.2,
          genericsReply.2.2, markerReply.2.2, defaultReply.2.2] using
          headReply.1
      have whereValid : Option.ValidFor WhereClause.ValidFor input.file
          parsedWhereClause := by
        simpa [headReply.2.2, argumentsReply.2.2, nameReply.2.2,
          genericsReply.2.2, markerReply.2.2, defaultReply.2.2] using
          whereReply.1
      have bodyValid : ImplInternals.ImplBody.ValidFor statementValid
          input.file body := by
        simpa [whereReply.2.2, headReply.2.2, argumentsReply.2.2,
          nameReply.2.2, genericsReply.2.2, markerReply.2.2,
          defaultReply.2.2] using bodyReply.1
      rcases ImplInternals.implBody_startsAtCurrentTokenOnSuccess afterWhere
          body afterBody bodyResult with
        ⟨opening, openingFound, bodyStart⟩
      have openingAtAfter :=
        State.getElem?_eq_some_of_peek?_eq_some openingFound
      have defaultTokens :=
        ImplInternals.implDefaultMarker_preservesTokensOnSuccess input
          defaultMarker afterDefault defaultResult
      have markerTokens := contextual_preservesTokensOnSuccess .impl .topItem
        afterDefault marker afterMarker markerResult
      have genericsTokens := optionalGenericParameters_preservesTokensOnSuccess
        afterMarker genericParameters afterGenerics genericsResult
      have nameTokens := identifier_preservesTokensOnSuccess .topItem
        afterGenerics traitName afterName nameResult
      have argumentsTokens := delimited_preservesTokensOnSuccess .less .greater
        false typeExpr .typeExpr .topLevel typeExpr_preservesTokensOnSuccess
        afterName arguments afterArguments argumentsResult
      have headTokens :=
        (ImplInternals.requireImplArguments_preservesTokenWindow arguments
          ).preservesTokensOnSuccess afterArguments headArguments afterHead
            headResult
      have whereTokens := whereClause_preservesTokensOnSuccess afterHead
        parsedWhereClause afterWhere whereResult
      have openingAt : input.tokens[afterWhere.cursor]? = some opening := by
        simpa [whereTokens, headTokens, argumentsTokens, nameTokens,
          genericsTokens, markerTokens, defaultTokens] using openingAtAfter
      have progress : input.cursor < afterWhere.cursor :=
        Nat.lt_of_le_of_lt
          (ImplInternals.implDefaultMarker_cursorMonotoneOnSuccess input
            defaultMarker afterDefault defaultResult)
          (Nat.lt_of_lt_of_le
            (acceptToken_cursor_lt_onSuccess (.contextual .impl) .topItem
              (fun kind => kind.isContextual .impl) markerResult)
            (Nat.le_trans
              (optionalGenericParameters_cursorMonotoneOnSuccess afterMarker
                genericParameters afterGenerics genericsResult)
              (Nat.le_trans
                (identifier_cursorMonotoneOnSuccess .topItem afterGenerics
                  traitName afterName nameResult)
                (Nat.le_trans
                  (delimited_cursorMonotoneOnSuccess .less .greater false
                    typeExpr .typeExpr .topLevel afterName arguments
                    afterArguments argumentsResult)
                  (Nat.le_trans
                    (ImplInternals.requireImplArguments_cursorMonotoneOnSuccess
                      arguments afterArguments headArguments afterHead
                      headResult)
                    (whereClause_cursorMonotoneOnSuccess afterHead
                      parsedWhereClause afterWhere whereResult))))))
      rcases implDecl_startsAtCurrentTokenOnSuccess input declaration final
          parsed with ⟨startToken, startFound, declarationStart⟩
      cases finished
      have startAt := State.getElem?_eq_some_of_peek?_eq_some startFound
      have startTokenValid := inputValid.peek?_span_validFor startFound
      have separated := inputValid.token_end_le_token_start_of_getElem?_lt
        startAt openingAt progress
      let startSpan := defaultMarker.getD marker.span
      have startValid : startSpan.ValidFor input.file := by
        cases defaultMarker with
        | none => simpa [startSpan] using markerValid
        | some retained =>
            simpa [startSpan, Option.ValidFor] using defaultValid
      have startTokenStart :
          startToken.span.startByte = startSpan.startByte := by
        simpa [startSpan, SourceSpan.cover] using declarationStart
      have ordered : startSpan.startByte ≤ body.span.endByte := by
        calc
          startSpan.startByte = startToken.span.startByte := startTokenStart.symm
          _ ≤ startToken.span.endByte := startTokenValid.2.1
          _ ≤ opening.span.startByte := separated
          _ = body.span.startByte := bodyStart
          _ ≤ body.span.endByte := bodyValid.1.2.1
      have outerValid := SourceSpan.cover_validFor startValid bodyValid.1 ordered
      refine ⟨⟨outerValid, ?_, ?_, ?_, nameValid, headValid.1,
        headValid.2, ?_, bodyValid.1, bodyValid.2⟩,
        weakResult.2.1, weakResult.2.2⟩
      · intro retained member
        cases defaultMarker with
        | none => simp at member
        | some marker =>
            have retainedEq : retained = marker := by simpa using member.symm
            subst retained
            simpa [Option.ValidFor] using defaultValid
      · intro retained member
        cases genericParameters with
        | none => simp at member
        | some parameters =>
            have retainedEq : retained = parameters := by simpa using member.symm
            subst retained
            simpa [Option.ValidFor] using genericsValid.1
      · intro retained member parameter parameterMember
        cases genericParameters with
        | none => simp at member
        | some parameters =>
            have retainedEq : retained = parameters := by simpa using member.symm
            subst retained
            exact genericsValid.2 parameter parameterMember
      · intro clause member
        cases parsedWhereClause with
        | none => simp at member
        | some retained =>
            simp at member
            subst clause
            simpa [Option.ValidFor] using whereValid

end Solcore.Syntax.Parser
