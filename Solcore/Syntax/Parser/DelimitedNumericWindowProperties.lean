import Solcore.Syntax.Parser.Delimited

/-! Numeric endpoint frames forget source, token carriers, and the byte end.
Both ordinary outcomes preserve only endIndex; invariants impose no condition.
This weaker frame lifts through delimiter loops without validity or progress
assumptions on the child. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

def Reply.PreservesEndIndex {α : Type} (reply : Reply α) (input : State) : Prop :=
  match reply with
  | .ok _ output | .reject _ output => output.window.endIndex = input.window.endIndex
  | .invariant _ => True

def Parser.PreservesEndIndex {α : Type} (parser : Parser α) : Prop :=
  ∀ input, (parser input).PreservesEndIndex input

theorem Reply.PreservesEndIndex.trans {α : Type} {reply : Reply α} {middle input : State}
    (held : reply.PreservesEndIndex middle) (frame : middle.window.endIndex = input.window.endIndex) :
    reply.PreservesEndIndex input := by
  cases reply with
  | ok value output | reject failure output => exact Eq.trans held frame
  | invariant error => trivial

theorem Parser.PreservesEndIndex.of_success_reject {α : Type} {parser : Parser α}
    (success : ∀ {input output value}, parser input = .ok value output → output.window.endIndex = input.window.endIndex)
    (reject : ∀ {input rejected failure}, parser input = .reject failure rejected → rejected.window.endIndex = input.window.endIndex) :
    Parser.PreservesEndIndex parser := by
  intro input
  cases result : parser input with
  | ok value output => exact success result
  | reject failure rejected => exact reject result
  | invariant error => trivial

theorem Parser.PreservesEndIndex.endIndex_eq_of_ok {α : Type} {parser : Parser α}
    (frame : Parser.PreservesEndIndex parser) {input output : State} {value : α}
    (result : parser input = .ok value output) : output.window.endIndex = input.window.endIndex := by
  have held := frame input
  simpa only [result, Reply.PreservesEndIndex] using held

theorem Parser.PreservesEndIndex.endIndex_eq_of_reject {α : Type} {parser : Parser α}
    (frame : Parser.PreservesEndIndex parser) {input rejected : State} {failure : Failure}
    (result : parser input = .reject failure rejected) : rejected.window.endIndex = input.window.endIndex := by
  have held := frame input
  simpa only [result, Reply.PreservesEndIndex] using held

theorem Parser.PreservesTokenWindow.preservesEndIndex {α : Type} {parser : Parser α}
    (frame : Parser.PreservesTokenWindow parser) : Parser.PreservesEndIndex parser := by
  intro input
  have held := frame input
  cases result : parser input <;> simp only [result, Reply.PreservesTokenWindow, Reply.PreservesEndIndex] at held ⊢
  · exact congrArg TokenWindow.endIndex held.2
  · exact congrArg TokenWindow.endIndex held.2

theorem pure_preservesEndIndex {α : Type} (value : α) : Parser.PreservesEndIndex (pure value) := fun _ => rfl

theorem bind_preservesEndIndex {α β : Type} {first : Parser α} {next : α → Parser β}
    (firstFrame : Parser.PreservesEndIndex first) (nextFrame : ∀ value, Parser.PreservesEndIndex (next value)) :
    Parser.PreservesEndIndex (first >>= next) := by
  intro input
  change (match first input with
    | .ok value middle => next value middle
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error).PreservesEndIndex input
  cases result : first input with
  | invariant error => trivial
  | reject failure rejected => exact firstFrame.endIndex_eq_of_reject result
  | ok value middle => exact (nextFrame value middle).trans (firstFrame.endIndex_eq_of_ok result)

theorem closeDelimited_preservesEndIndex {α : Type} (opening : Token) (closing : Symbol)
    (context : ParseContext) (values : List α) :
    Parser.PreservesEndIndex (closeDelimited opening closing context values) := by
  intro input
  unfold closeDelimited
  have held := (symbol_preservesTokenWindow closing context).preservesEndIndex input
  cases result : symbol closing context input <;> simp only [result, Reply.PreservesEndIndex] at held ⊢ <;> exact held

theorem afterDelimitedElement_preservesEndIndex {α : Type} (element : Parser α)
    (child : Parser.PreservesEndIndex element) (closing : Symbol) (trailing : Bool)
    (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel values, Parser.PreservesEndIndex (afterDelimitedElement element closing trailing context phase opening fuel values) := by
  intro fuel
  induction fuel with
  | zero => intro values input; trivial
  | succ fuel ih =>
      intro values input
      unfold afterDelimitedElement
      split
      · cases commaResult : symbol .comma context input with
        | invariant error => trivial
        | reject failure rejected => exact (symbol_preservesTokenWindow .comma context).preservesEndIndex.endIndex_eq_of_reject commaResult
        | ok comma afterComma =>
            have commaFrame := (symbol_preservesTokenWindow .comma context).preservesEndIndex.endIndex_eq_of_ok commaResult
            simp only
            split
            · exact (closeDelimited_preservesEndIndex opening closing context values afterComma).trans commaFrame
            · cases childResult : element afterComma with
              | invariant error => trivial
              | reject failure rejected => exact (child.endIndex_eq_of_reject childResult).trans commaFrame
              | ok value next =>
                  simp only
                  split
                  · exact (ih (value :: values) next).trans ((child.endIndex_eq_of_ok childResult).trans commaFrame)
                  · trivial
      · split
        · exact closeDelimited_preservesEndIndex opening closing context values input
        · exact rfl

theorem delimitedWithPolicy_preservesEndIndex {α : Type} (opening closing : Symbol)
    (empty trailing : Bool) (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (child : Parser.PreservesEndIndex element) :
    Parser.PreservesEndIndex (delimitedWithPolicy opening closing empty trailing element context phase) := by
  intro input
  unfold delimitedWithPolicy
  cases openingResult : symbol opening context input with
  | invariant error => trivial
  | reject failure rejected => exact (symbol_preservesTokenWindow opening context).preservesEndIndex.endIndex_eq_of_reject openingResult
  | ok marker afterOpening =>
      have openingFrame := (symbol_preservesTokenWindow opening context).preservesEndIndex.endIndex_eq_of_ok openingResult
      simp only
      split
      · exact (closeDelimited_preservesEndIndex marker closing context [] afterOpening).trans openingFrame
      · cases childResult : element afterOpening with
        | invariant error => trivial
        | reject failure rejected => exact (child.endIndex_eq_of_reject childResult).trans openingFrame
        | ok value next =>
            simp only
            split
            · exact (afterDelimitedElement_preservesEndIndex element child closing trailing context phase marker
                (afterOpening.remainingCount + 1) [value] next).trans ((child.endIndex_eq_of_ok childResult).trans openingFrame)
            · trivial

end Solcore.Syntax.Parser
