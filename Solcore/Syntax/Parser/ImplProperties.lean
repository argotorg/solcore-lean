import Solcore.Syntax.Parser.Impl
import Solcore.Syntax.Parser.FunctionProperties

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

end Solcore.Syntax.Parser
