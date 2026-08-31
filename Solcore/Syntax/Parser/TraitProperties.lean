import Solcore.Syntax.Parser.Trait

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
