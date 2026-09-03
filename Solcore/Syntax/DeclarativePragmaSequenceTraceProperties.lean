import Solcore.Syntax.DeclarativePragmaSequenceTraceGrammar
import Solcore.Syntax.DeclarativePragmaTraceProperties
import Solcore.Syntax.DeclarativeFileItemsOutcomeGrammar

/-! Carrier, progress, exactness, and ordinary-file erasure for independent
pragma-only sequences. Traces and written declaration order are retained. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem pragmaTail_shape {input output : Remainder}
    {items : List Syntax.Identifier}
    (parsed : PragmaItemsTailOrdinaryParses input items output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex ∧
      input.cursor ≤ output.cursor := by
  induction parsed with
  | done => exact ⟨rfl, rfl, Nat.le_refl _⟩
  | trailing _ _ comma _ =>
      rw [comma.2]
      exact ⟨rfl, rfl, by simp⟩
  | next _ _ comma _ item _ ih =>
      rcases comma with ⟨_, rfl⟩
      exact ⟨ih.1.trans item.2.1, ih.2.1.trans item.2.2.1,
        by have advance := item.2.2.2; have monotone := ih.2.2; simp only at advance; omega⟩

private theorem pragmaItems_shape {input output : Remainder}
    {items : List Syntax.Identifier}
    (parsed : PragmaItemsOrdinaryParses input items output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex ∧
      input.cursor ≤ output.cursor := by
  cases parsed with
  | empty => exact ⟨rfl, rfl, Nat.le_refl _⟩
  | nonempty _ first tail =>
      have tailShape := pragmaTail_shape tail
      exact ⟨tailShape.1.trans first.2.1, tailShape.2.1.trans first.2.2.1,
        by have advance := first.2.2.2; have monotone := tailShape.2.2; omega⟩

/-- The marker starts inside the active window, independently of diagnostics. -/
theorem PragmaDeclOrdinaryParses.startsInside
    {input output : Remainder} {declaration : Syntax.PragmaDecl}
    (parsed : PragmaDeclOrdinaryParses input declaration output) :
    input.cursor < input.endIndex := by
  cases parsed with
  | parsed _ _ marker _ _ _ => exact marker.1.1

/-- Successful pragma grammar preserves its carrier and active end, makes
strict progress, and never consumes beyond the active window. -/
theorem PragmaDeclOrdinaryParses.carrier_progress
    {input output : Remainder} {declaration : Syntax.PragmaDecl}
    (parsed : PragmaDeclOrdinaryParses input declaration output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex ∧
      input.cursor < output.cursor ∧ output.cursor ≤ input.endIndex := by
  cases parsed with
  | parsed _ _ marker name items semicolon =>
      rcases marker with ⟨_, rfl⟩
      have itemsShape := pragmaItems_shape items
      rcases semicolon with ⟨inside, rfl⟩
      have tokensEq := itemsShape.1.trans name.2.1
      have endEq := itemsShape.2.1.trans name.2.2.1
      have advance := name.2.2.2
      have monotone := itemsShape.2.2
      simp only at tokensEq endEq advance ⊢
      exact ⟨tokensEq, endEq, by omega, by have bound := inside.1; omega⟩

/-- A fixed pragma token selects its plain top-item branch and excludes hash,
import, and export priority guards without executable lookahead premises. -/
theorem PragmaDeclOrdinaryParses.toTopItem
    {input output : Remainder} {declaration : Syntax.PragmaDecl}
    (parsed : PragmaDeclOrdinaryParses input declaration output) :
    TopItemOrdinaryParses input (pragmaSequenceItem declaration) output := by
  have marker : ∃ span, TokenAt input.tokens input.endIndex input.cursor
      { span, value := .keyword .pragmaKw } := by
    cases parsed with
    | parsed span _ present _ _ _ => exact ⟨span, present.1⟩
  rcases marker with ⟨span, present⟩
  have absent (kind : TokenKind) (different : kind ≠ .keyword .pragmaKw) :
      TokenKindAbsentAt input.tokens input.endIndex input.cursor kind := by
    rintro ⟨otherSpan, other⟩
    exact different (congrArg (fun token : Token => token.value) (other.token_unique present))
  exact .plain (absent (.symbol .hash) (by decide))
    (.pragmaDecl (.pragmaDecl (absent (.keyword .importKw) (by decide))
      (absent (.keyword .exportKw) (by decide)) ⟨span, present⟩) parsed)

/-- The complete independent scan retains its carrier/end and finishes at or
past that same window end; an empty input may already be past it. -/
theorem PragmaSequenceTraceParses.carrier_atEnd
    {input output : Remainder} {declarations : List Syntax.PragmaDecl}
    {trace : List ParseDiagnostic}
    (parsed : PragmaSequenceTraceParses input declarations output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex ∧
      input.endIndex ≤ output.cursor := by
  induction parsed with
  | done atEnd => exact ⟨rfl, rfl, atEnd⟩
  | cons head _ ih =>
      have headShape := head.1.carrier_progress
      exact ⟨ih.1.trans headShape.1, ih.2.1.trans headShape.2.1,
        by simpa only [headShape.2.1] using ih.2.2⟩

/-- Declaration count is bounded by remaining tokens, without a token-array
validity assumption. This can later justify an executor's chosen fuel. -/
theorem PragmaSequenceTraceParses.length_le_remaining
    {input output : Remainder} {declarations : List Syntax.PragmaDecl}
    {trace : List ParseDiagnostic}
    (parsed : PragmaSequenceTraceParses input declarations output trace) :
    declarations.length ≤ input.endIndex - input.cursor := by
  induction parsed with
  | done => simp
  | cons head _ ih =>
      have shape := head.1.carrier_progress
      simp only [List.length_cons]
      omega

/-- Erasing trace information yields the existing ordinary file-item grammar
with the same written-order pragma AST list and exact endpoint. -/
theorem PragmaSequenceTraceParses.toFileItems
    {input output : Remainder} {declarations : List Syntax.PragmaDecl}
    {trace : List ParseDiagnostic}
    (parsed : PragmaSequenceTraceParses input declarations output trace) :
    FileItemsOrdinaryParses input (pragmaSequenceItems declarations) output := by
  induction parsed with
  | done atEnd => exact .done atEnd
  | cons head _ ih =>
      exact .direct head.1.startsInside head.1.toTopItem head.1.carrier_progress.2.2.1 ih

/-- The independent scan fixes the entire declaration list, remainder, and
diagnostic trace, preserving duplicates as well as source order. -/
theorem PragmaSequenceTraceParses.result_unique
    {input leftOutput rightOutput : Remainder}
    {left right : List Syntax.PragmaDecl} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : PragmaSequenceTraceParses input left leftOutput leftTrace)
    (rightParsed : PragmaSequenceTraceParses input right rightOutput rightTrace) :
    left = right ∧ leftOutput = rightOutput ∧ leftTrace = rightTrace := by
  induction leftParsed generalizing right rightOutput rightTrace with
  | done atEnd =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl, rfl⟩
      | cons head _ => have inside := head.1.startsInside; omega
  | cons leftHead leftTail ih =>
      cases rightParsed with
      | done atEnd => have inside := leftHead.1.startsInside; omega
      | cons rightHead rightTail =>
          rcases leftHead.result_unique rightHead with ⟨rfl, rfl, rfl⟩
          rcases ih rightTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
