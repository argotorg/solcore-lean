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

end Solcore.Syntax.Parser
