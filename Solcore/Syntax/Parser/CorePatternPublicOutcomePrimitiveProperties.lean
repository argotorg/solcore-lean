import Solcore.Syntax.Parser.CorePatternBoundaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.PatternRecoveryTotalityProperties

/-! Shared executable primitives for public Core pattern outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Preserved carrier and active window make a cursor-only rewind exact. -/
theorem rewoundPattern_declarativeRemainder_eq
    (input failed : State)
    (shape : failed.tokens = input.tokens ∧ failed.window = input.window) :
    ({ failed with cursor := input.cursor } : State).declarativeRemainder =
      input.declarativeRemainder := by
  unfold State.declarativeRemainder
  simp only
  rw [shape.1, shape.2]

/-- A Core rejection plus its window contract supplies the declarative
rewind witness. -/
theorem patternCoreRejectsWithPreservedWindow_of_result
    (nested : Parser Pattern) (expression : Parser Expr)
    (coreRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (coreRejectSound : ∀ {input rejected : State} {failure : Failure},
      patternCore nested expression input = .reject failure rejected →
        coreRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (coreWindow : Parser.PreservesTokenWindow
      (patternCore nested expression))
    {input failed : State} {failure : Failure}
    (result : patternCore nested expression input = .reject failure failed) :
    DeclarativeGrammar.PatternCoreRejectsWithPreservedWindow coreRejects
      input.declarativeRemainder := by
  have resultShape := coreWindow input
  rw [result] at resultShape
  have shape : failed.tokens = input.tokens ∧
      failed.window = input.window := by
    simpa only [Reply.PreservesTokenWindow] using resultShape
  exact ⟨failed.declarativeRemainder, coreRejectSound result, shape.1,
    congrArg TokenWindow.endIndex shape.2⟩

/-- Successful advancement exposes its token and cursor-only successor. -/
theorem advance?_eq_some_shape {input next : State} {token : Token}
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

/-- Failed first advancement is the exact non-consuming recovery rejection. -/
theorem patternRecoveryRejects_of_advance?_eq_none
    (input : State) (advanced : input.advance? = none) :
    DeclarativeGrammar.PatternRecoveryRejects
      input.declarativeRemainder input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have inside : input.cursor < input.window.endIndex := by omega
    apply DeclarativeGrammar.PatternRecoveryRejects.missingToken inside
    unfold State.advance? State.peek? at advanced
    simpa [State.declarativeRemainder, inside] using advanced

/-- Package the mandatory first token and a successful emitted recovery scan. -/
theorem patternRecoveryParses_of_aux_success
    {input next output : State} {token : Token} {failure : Failure}
    {pattern : Pattern}
    (advanced : input.advance? = some (token, next))
    (result : recoverPatternAux token.span token.span
      (next.remainingCount + 1) (next.emit failure.toDiagnostic) =
        .ok pattern output) :
    DeclarativeGrammar.PatternRecoveryParses input.declarativeRemainder
      pattern output.declarativeRemainder := by
  rcases advance?_eq_some_shape advanced with ⟨found, nextEq⟩
  have scan := recoverPatternAux_success_ordinary_sound token.span
    (next.remainingCount + 1) token.span (next.emit failure.toDiagnostic)
      pattern output result
  have emittedEq :
      (next.emit failure.toDiagnostic).declarativeRemainder =
        next.declarativeRemainder := by
    rfl
  rw [emittedEq, nextEq] at scan
  exact .recovered (tokenAt_of_peek?_eq_some found) scan

end Solcore.Syntax.Parser.PatternInternals
