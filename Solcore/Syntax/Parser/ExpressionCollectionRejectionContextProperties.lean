import Solcore.Syntax.Parser.ExpressionNameRejectionTraceProperties
import Solcore.Syntax.Parser.ExpressionDiagnosticTraceContracts
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! Collection rejection preserves the file and any chosen window observation.
Taking the identity observes the full window; taking endByte allows endIndex
to change on rejection. Children may replace tokens, move arbitrarily, or
return invariants. No validity, diagnostic, ordinary, or carrier law is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {β : Type} {view : TokenWindow → β}

private def KeepsContext {α : Type} (reply : Reply α) (input : State) : Prop :=
  match reply with
  | .ok _ output | .reject _ output => output.file = input.file ∧ view output.window = view input.window
  | .invariant _ => True

private theorem context_trans {α : Type} {reply : Reply α} {middle input : State}
    (held : KeepsContext (view := view) reply middle)
    (frame : middle.file = input.file ∧ view middle.window = view input.window) : KeepsContext (view := view) reply input := by
  cases reply with
  | ok value output => exact ⟨held.1.trans frame.1, held.2.trans frame.2⟩
  | reject failure output => exact ⟨held.1.trans frame.1, held.2.trans frame.2⟩
  | invariant error => trivial

private theorem context_bind {α β : Type} {first : Parser α} {next : α → Parser β}
    (firstFrame : ∀ input, KeepsContext (view := view) (first input) input)
    (nextFrame : ∀ value input, KeepsContext (view := view) (next value input) input) :
    ∀ input, KeepsContext (view := view) ((first >>= next) input) input := by
  intro input
  have held := firstFrame input
  change KeepsContext (view := view) (match first input with
    | .ok value middle => next value middle
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) input
  cases result : first input with
  | invariant error => trivial
  | reject failure rejected => simpa only [result, KeepsContext] using held
  | ok value middle => exact context_trans (view := view) (nextFrame value middle) (by simpa only [result, KeepsContext] using held)

private theorem symbol_context (kind : Symbol) (context : ParseContext) (input : State) :
    KeepsContext (view := view) (symbol kind context input) input := by
  cases result : symbol kind context input with
  | invariant error => trivial
  | reject failure rejected => rw [symbol_reject_state_eq kind context result]; exact ⟨rfl, rfl⟩
  | ok value output => rw [(symbol_ok_tokenAt kind context result).2]; exact ⟨rfl, rfl⟩

private theorem closeDelimited_context {α : Type} (opening : Token) (closing : Symbol)
    (context : ParseContext) (values : List α) (input : State) :
    KeepsContext (view := view) (closeDelimited opening closing context values input) input := by
  have frame := symbol_context (view := view) closing context input
  unfold closeDelimited
  cases result : symbol closing context input <;> simp only [result, KeepsContext] at frame ⊢ <;> exact frame

private theorem delimitedTail_context {α : Type} (element : Parser α)
    (child : ∀ input, KeepsContext (view := view) (element input) input)
    (closing : Symbol) (trailing : Bool) (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel values input, KeepsContext (view := view) (afterDelimitedElement element closing trailing context phase opening
      fuel values input) input := by
  intro fuel
  induction fuel with
  | zero => intro values input; trivial
  | succ fuel ih =>
      intro values input
      unfold afterDelimitedElement
      split
      · have commaFrame := symbol_context (view := view) .comma context input
        cases commaResult : symbol .comma context input with
        | invariant error => trivial
        | reject failure rejected => simpa only [commaResult, KeepsContext] using commaFrame
        | ok comma afterComma =>
            rw [commaResult] at commaFrame
            simp only
            split
            · exact context_trans (view := view) (closeDelimited_context (view := view) opening closing context values afterComma) commaFrame
            · have childFrame := child afterComma
              cases childResult : element afterComma with
              | invariant error => trivial
              | reject failure rejected =>
                  exact context_trans (view := view) (by simpa only [childResult, KeepsContext] using childFrame) commaFrame
              | ok value next =>
                  rw [childResult] at childFrame
                  simp only
                  split
                  · exact context_trans (view := view) (context_trans (view := view) (ih (value :: values) next) childFrame) commaFrame
                  · trivial
      · split
        · exact closeDelimited_context (view := view) opening closing context values input
        · exact ⟨rfl, rfl⟩

private theorem delimited_context {α : Type} (element : Parser α)
    (child : ∀ input, KeepsContext (view := view) (element input) input)
    (opening closing : Symbol) (empty trailing : Bool) (context : ParseContext) (phase : ParserPhase)
    (input : State) :
    KeepsContext (view := view) (delimitedWithPolicy opening closing empty trailing element context phase input) input := by
  have openingFrame := symbol_context (view := view) opening context input
  unfold delimitedWithPolicy
  cases openingResult : symbol opening context input with
  | invariant error => trivial
  | reject failure rejected => simpa only [openingResult, KeepsContext] using openingFrame
  | ok marker afterOpening =>
      rw [openingResult] at openingFrame
      simp only
      split
      · exact context_trans (view := view) (closeDelimited_context (view := view) marker closing context [] afterOpening) openingFrame
      · have childFrame := child afterOpening
        cases childResult : element afterOpening with
        | invariant error => trivial
        | reject failure rejected =>
            exact context_trans (view := view) (by simpa only [childResult, KeepsContext] using childFrame) openingFrame
        | ok value next =>
            rw [childResult] at childFrame
            simp only
            split
            · exact context_trans (view := view) (context_trans (view := view) (delimitedTail_context (view := view) element child closing trailing context phase
                marker (afterOpening.remainingCount + 1) [value] next) childFrame) openingFrame
            · trivial

private theorem closeTuple_context (opening : Token) (values : List Expr) (input : State) :
    KeepsContext (view := view) (closeTuple opening values input) input := by
  unfold closeTuple
  apply context_bind (view := view) (symbol_context (view := view) .rightParen .expression)
  intro closing next
  split <;> exact ⟨rfl, rfl⟩

private theorem tupleTail_context (nested : Parser Expr)
    (child : ∀ input, KeepsContext (view := view) (nested input) input) (opening : Token) :
    ∀ fuel values input, KeepsContext (view := view) (tupleTail nested opening fuel values input) input := by
  intro fuel
  induction fuel with
  | zero => intro values input; trivial
  | succ fuel ih =>
      intro values input
      have commaFrame := symbol_context (view := view) .comma .expression input
      unfold tupleTail
      cases commaResult : symbol .comma .expression input with
      | invariant error => trivial
      | reject failure rejected => simpa only [commaResult, KeepsContext] using commaFrame
      | ok comma afterComma =>
          rw [commaResult] at commaFrame
          simp only
          split
          · exact context_trans (view := view) (closeTuple_context (view := view) opening values afterComma) commaFrame
          · have childFrame := child afterComma
            cases childResult : nested afterComma with
            | invariant error => trivial
            | reject failure rejected =>
                exact context_trans (view := view) (by simpa only [childResult, KeepsContext] using childFrame) commaFrame
            | ok value next =>
                rw [childResult] at childFrame
                simp only
                split
                · split
                  · exact context_trans (view := view) (context_trans (view := view) (ih (value :: values) next) childFrame) commaFrame
                  · exact context_trans (view := view) (context_trans (view := view) (closeTuple_context (view := view) opening (value :: values) next)
                      childFrame) commaFrame
                · trivial

private theorem parenthesized_context (nested : Parser Expr)
    (child : ∀ input, KeepsContext (view := view) (nested input) input) (input : State) :
    KeepsContext (view := view) (parenthesized nested input) input := by
  have openingFrame := symbol_context (view := view) .leftParen .expression input
  unfold parenthesized
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => trivial
  | reject failure rejected => simpa only [openingResult, KeepsContext] using openingFrame
  | ok opening afterOpening =>
      rw [openingResult] at openingFrame
      simp only
      split
      · exact context_trans (view := view) (closeTuple_context (view := view) opening [] afterOpening) openingFrame
      · have childFrame := child afterOpening
        cases childResult : nested afterOpening with
        | invariant error => trivial
        | reject failure rejected =>
            exact context_trans (view := view) (by simpa only [childResult, KeepsContext] using childFrame) openingFrame
        | ok first next =>
            rw [childResult] at childFrame
            simp only
            split
            · trivial
            · split
              · exact context_trans (view := view) (context_trans (view := view) (tupleTail_context (view := view) nested child opening
                  (next.remainingCount + 1) [first] next) childFrame) openingFrame
              · exact context_trans (view := view) (context_trans (view := view) (closeTuple_context (view := view) opening [first] next) childFrame) openingFrame

private theorem optionalArguments_context (nested : Parser Expr)
    (child : ∀ input, KeepsContext (view := view) (nested input) input) (input : State) :
    KeepsContext (view := view) (optionalDotConstructorArguments nested input) input := by
  unfold optionalDotConstructorArguments
  simp only [bind, getState]
  split
  · apply context_bind (view := view) (delimited_context (view := view) nested child .leftParen .rightParen true false .expression .expression)
    intro value next; exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

private theorem expressionName_context (input : State) : KeepsContext (view := view) (expressionName input) input := by
  cases result : expressionName input with
  | invariant error => trivial
  | ok value output =>
      have frame := expressionName_success_context_eq result
      exact ⟨frame.1, congrArg view frame.2⟩
  | reject failure rejected => rw [(expressionName_reject_trace_sound result).2]; exact ⟨rfl, rfl⟩

private theorem child_context {nested : Parser Expr} (success : ∀ {input output value}, nested input = .ok value output →
      output.file = input.file ∧ view output.window = view input.window)
    (reject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window) (input : State) :
    KeepsContext (view := view) (nested input) input := by
  cases result : nested input with
  | invariant error => trivial
  | ok value output => exact success result
  | reject failure rejected => exact reject result

variable {nested : Parser Expr}

private theorem projected_success (success : ExpressionSuccessContext nested)
    {input output : State} {value : Expr} (result : nested input = .ok value output) :
    output.file = input.file ∧ view output.window = view input.window :=
  ⟨(success result).1, congrArg view (success result).2⟩

theorem parenthesized_reject_context_of_windowProjection (success : ExpressionSuccessContext nested)
    (reject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    {input rejected : State} {failure : Failure} (result : parenthesized nested input = .reject failure rejected) :
    rejected.file = input.file ∧ view rejected.window = view input.window := by
  have frame := parenthesized_context (view := view) nested
    (child_context (view := view) (projected_success success) reject) input
  simpa only [result, KeepsContext] using frame

theorem arrayLiteral_reject_context_of_windowProjection (success : ExpressionSuccessContext nested)
    (reject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    {input rejected : State} {failure : Failure} (result : arrayLiteral nested input = .reject failure rejected) :
    rejected.file = input.file ∧ view rejected.window = view input.window := by
  have frame : KeepsContext (view := view) (arrayLiteral nested input) input := by
    unfold arrayLiteral
    apply context_bind (view := view) (delimited_context (view := view) nested
      (child_context (view := view) (projected_success success) reject)
      .leftBracket .rightBracket true false .expression .expression)
    intro value next; exact ⟨rfl, rfl⟩
  simpa only [result, KeepsContext] using frame

theorem dotConstructor_reject_context_of_windowProjection (success : ExpressionSuccessContext nested)
    (reject : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ view rejected.window = view input.window)
    {input rejected : State} {failure : Failure} (result : dotConstructor nested input = .reject failure rejected) :
    rejected.file = input.file ∧ view rejected.window = view input.window := by
  have frame : KeepsContext (view := view) (dotConstructor nested input) input := by
    unfold dotConstructor
    apply context_bind (view := view) (symbol_context (view := view) .dot .expression)
    intro dot
    apply context_bind (view := view) (expressionName_context (view := view))
    intro name
    apply context_bind (view := view) (optionalArguments_context (view := view) nested
      (child_context (view := view) (projected_success success) reject))
    intro value next; exact ⟨rfl, rfl⟩
  simpa only [result, KeepsContext] using frame

end Solcore.Syntax.Parser.ExpressionAtomInternals
