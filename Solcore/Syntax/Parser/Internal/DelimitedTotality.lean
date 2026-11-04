import Solcore.Syntax.Parser.Internal.Basics

/-!
Totality of the parsers of delimited lists and primitives: on valid input they make
progress and end in an ordinary outcome.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedNumericWindowProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedTotalityProperties
/-! Conditional totality for generic delimited parser loops. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Minimal valid-input contract needed to exclude delimited-loop invariants. -/
structure ElementTotalityContract {α : Type} (element : Parser α) : Prop where
  validFor : element.ValidFor (fun _ _ => True)
  preservesTokenWindow : Parser.PreservesTokenWindow element
  cursorLtOnSuccess : ∀ {input next : State} {value : α},
    element input = .ok value next → input.cursor < next.cursor
  invariantFree : ∀ input, input.ValidFor → ∀ error,
    element input ≠ .invariant error

private theorem symbol_ordinary_variant (value : Symbol) (context : ParseContext)
    (state : State) :
    (∃ token next, symbol value context state = .ok token next) ∨
      (∃ failure next, symbol value context state = .reject failure next) := by
  cases result : symbol value context state with
  | ok token next => exact Or.inl ⟨token, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      unfold symbol acceptToken at result
      cases found : state.peek? with
      | none => simp [found, rejectAt] at result
      | some token =>
          simp only [found] at result
          split at result <;> contradiction

private theorem symbol_ne_invariant_variant (value : Symbol) (context : ParseContext)
    (state : State) (error : ParserInvariantError) :
    symbol value context state ≠ .invariant error := by
  intro failed
  rcases symbol_ordinary_variant value context state with
    ⟨token, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

private theorem closeDelimited_ordinary {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) (state : State) :
    (∃ values next,
      closeDelimited opening closing context elementsRev state =
        .ok values next) ∨
      (∃ failure next,
        closeDelimited opening closing context elementsRev state =
          .reject failure next) := by
  unfold closeDelimited
  rcases symbol_ordinary_variant closing context state with
    ⟨token, next, result⟩ | ⟨failure, next, result⟩
  · rw [result]
    exact Or.inl ⟨_, _, rfl⟩
  · rw [result]
    exact Or.inr ⟨_, _, rfl⟩

private theorem remainingCount_lt_after_strict_progress_variant
    {input next : State} {fuel : Nat}
    (nextValid : next.ValidFor) (windowEq : next.window = input.window)
    (progress : input.cursor < next.cursor)
    (adequate : input.remainingCount < fuel + 1) :
    next.remainingCount < fuel := by
  have nextCursorBound : next.cursor ≤ input.window.endIndex := by
    simpa [windowEq] using nextValid.cursor_le_endIndex
  have endIndexEq : next.window.endIndex = input.window.endIndex :=
    congrArg TokenWindow.endIndex windowEq
  simp only [State.remainingCount] at adequate ⊢
  rw [endIndexEq]
  omega

/--
Adequate fuel makes the generic tail loop ordinary: it either closes the list
or reports a source rejection, but cannot exhaust fuel or fail progress.
-/
theorem afterDelimitedElement_ordinary_of_remainingCount_lt {α : Type}
    (element : Parser α) (contract : ElementTotalityContract element)
    (closing : Symbol) (allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev state,
      state.ValidFor → state.remainingCount < fuel →
      (∃ values next,
        afterDelimitedElement element closing allowTrailing context phase
          opening fuel elementsRev state = .ok values next) ∨
      (∃ failure next,
        afterDelimitedElement element closing allowTrailing context phase
          opening fuel elementsRev state = .reject failure next) := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev state stateValid adequate
      omega
  | succ fuel inductionHypothesis =>
      intro elementsRev state stateValid adequate
      unfold afterDelimitedElement
      split
      · cases commaResult : symbol .comma context state with
        | ok comma afterComma =>
          have commaValid := symbol_validFor .comma context state stateValid
          rw [commaResult] at commaValid
          dsimp only
          split
          · exact closeDelimited_ordinary opening closing context elementsRev
              afterComma
          · cases elementResult : element afterComma with
            | invariant error =>
                exact False.elim
                  (contract.invariantFree afterComma commaValid.2.1 error
                    elementResult)
            | reject failure rejected =>
                exact Or.inr ⟨failure, rejected, rfl⟩
            | ok value next =>
                have valueReply := contract.validFor afterComma commaValid.2.1
                rw [elementResult] at valueReply
                have valueWindow := contract.preservesTokenWindow afterComma
                rw [elementResult] at valueWindow
                have progress := contract.cursorLtOnSuccess elementResult
                dsimp only
                split
                · have afterCommaWindow : afterComma.window = state.window := by
                    rw [(symbol_ok_state_shape .comma context commaResult).2]
                  have nextWindow : next.window = state.window :=
                    valueWindow.2.trans afterCommaWindow
                  have commaProgress : state.cursor < afterComma.cursor := by
                    rw [(symbol_ok_state_shape .comma context commaResult).2]
                    simp
                  have nextAdequate :=
                    remainingCount_lt_after_strict_progress_variant valueReply.2.1
                      nextWindow (Nat.lt_trans commaProgress progress) adequate
                  exact inductionHypothesis (value :: elementsRev) next
                    valueReply.2.1 nextAdequate
                · omega
        | reject failure rejected =>
          exact Or.inr ⟨failure, rejected, rfl⟩
        | invariant error =>
          exact False.elim
            (symbol_ne_invariant_variant .comma context state error commaResult)
      · split
        · exact closeDelimited_ordinary opening closing context elementsRev
            state
        · exact Or.inr ⟨_, _, rfl⟩

/-- Adequate tail-loop fuel rules out every invariant result explicitly. -/
theorem afterDelimitedElement_ne_invariant_of_remainingCount_lt {α : Type}
    (element : Parser α) (contract : ElementTotalityContract element)
    (closing : Symbol) (allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (fuel : Nat) (elementsRev : List α) (state : State)
    (stateValid : state.ValidFor) (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    afterDelimitedElement element closing allowTrailing context phase opening
      fuel elementsRev state ≠ .invariant error := by
  intro failed
  rcases afterDelimitedElement_ordinary_of_remainingCount_lt element contract
      closing allowTrailing context phase opening fuel elementsRev state
      stateValid adequate with
    ⟨values, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Delimiter-policy execution is ordinary on every valid input. -/
theorem delimitedWithPolicy_ordinary {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (contract : ElementTotalityContract element) (input : State)
    (inputValid : input.ValidFor) :
    (∃ values next,
      delimitedWithPolicy opening closing allowEmpty allowTrailing element
        context phase input = .ok values next) ∨
      (∃ failure next,
        delimitedWithPolicy opening closing allowEmpty allowTrailing element
          context phase input = .reject failure next) := by
  unfold delimitedWithPolicy
  cases openingResult : symbol opening context input with
  | ok openingToken afterOpening =>
    have openingValid := symbol_validFor opening context input inputValid
    rw [openingResult] at openingValid
    dsimp only
    split
    · exact closeDelimited_ordinary openingToken closing context [] afterOpening
    · cases elementResult : element afterOpening with
      | invariant error =>
          exact False.elim
            (contract.invariantFree afterOpening openingValid.2.1 error
              elementResult)
      | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
      | ok value next =>
          have valueReply := contract.validFor afterOpening openingValid.2.1
          rw [elementResult] at valueReply
          have valueWindow := contract.preservesTokenWindow afterOpening
          rw [elementResult] at valueWindow
          have progress := contract.cursorLtOnSuccess elementResult
          dsimp only
          split
          · have adequate :
                next.remainingCount < afterOpening.remainingCount + 1 := by
              apply remainingCount_lt_after_strict_progress_variant valueReply.2.1
                valueWindow.2 progress
              omega
            exact afterDelimitedElement_ordinary_of_remainingCount_lt element
              contract closing allowTrailing context phase openingToken
              (afterOpening.remainingCount + 1) [value] next
              valueReply.2.1 adequate
          · omega
  | reject failure rejected =>
    exact Or.inr ⟨failure, rejected, rfl⟩
  | invariant error =>
    exact False.elim
      (symbol_ne_invariant_variant opening context input error openingResult)

theorem delimitedWithPolicy_ne_invariant {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (contract : ElementTotalityContract element) (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    delimitedWithPolicy opening closing allowEmpty allowTrailing element
      context phase input ≠ .invariant error := by
  intro failed
  rcases delimitedWithPolicy_ordinary opening closing allowEmpty allowTrailing
      element context phase contract input inputValid with
    ⟨values, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

theorem delimited_ordinary {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    (contract : ElementTotalityContract element) (input : State)
    (inputValid : input.ValidFor) :
    (∃ values next,
      delimited opening closing allowEmpty element context phase input =
        .ok values next) ∨
      (∃ failure next,
        delimited opening closing allowEmpty element context phase input =
          .reject failure next) :=
  delimitedWithPolicy_ordinary opening closing allowEmpty true element context
    phase contract input inputValid

theorem delimited_ne_invariant {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    (contract : ElementTotalityContract element) (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    delimited opening closing allowEmpty element context phase input ≠
      .invariant error :=
  delimitedWithPolicy_ne_invariant opening closing allowEmpty true element
    context phase contract input inputValid error

theorem delimitedNoTrailing_ordinary {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    (contract : ElementTotalityContract element) (input : State)
    (inputValid : input.ValidFor) :
    (∃ values next,
      delimitedNoTrailing opening closing allowEmpty element context phase
        input = .ok values next) ∨
      (∃ failure next,
        delimitedNoTrailing opening closing allowEmpty element context phase
          input = .reject failure next) :=
  delimitedWithPolicy_ordinary opening closing allowEmpty false element context
    phase contract input inputValid

theorem delimitedNoTrailing_ne_invariant {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    (contract : ElementTotalityContract element) (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    delimitedNoTrailing opening closing allowEmpty element context phase input ≠
      .invariant error :=
  delimitedWithPolicy_ne_invariant opening closing allowEmpty false element
    context phase contract input inputValid error

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PrimitiveTotalityProperties
/-! Totality contracts for primitive token parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace Parser

/-- A parser has only ordinary success or rejection results. -/
def Ordinary {α : Type} (parser : Parser α) : Prop :=
  ∀ input,
    (∃ value next, parser input = .ok value next) ∨
      (∃ failure next, parser input = .reject failure next)

namespace Ordinary

/-- An ordinary parser cannot expose an internal invariant result. -/
theorem ne_invariant {α : Type} {parser : Parser α}
    (ordinary : Ordinary parser) (input : State)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error := by
  intro failed
  rcases ordinary input with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

end Ordinary
end Parser

/-- Generic token acceptance is ordinary for every predicate and input. -/
theorem acceptToken_ordinary (expected : ParseExpectation)
    (context : ParseContext) (accepts : TokenKind → Bool) :
    Parser.Ordinary (acceptToken expected context accepts) := by
  intro input
  cases result : acceptToken expected context accepts input with
  | ok token next => exact Or.inl ⟨token, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      unfold acceptToken at result
      cases found : input.peek? with
      | none => simp [found, rejectAt] at result
      | some token =>
          simp only [found] at result
          split at result <;> contradiction

theorem acceptToken_ne_invariant (expected : ParseExpectation)
    (context : ParseContext) (accepts : TokenKind → Bool)
    (input : State) (error : ParserInvariantError) :
    acceptToken expected context accepts input ≠ .invariant error :=
  (acceptToken_ordinary expected context accepts).ne_invariant input error

theorem keyword_ordinary (value : HardKeyword) (context : ParseContext) :
    Parser.Ordinary (keyword value context) :=
  acceptToken_ordinary (.keyword value) context (· == .keyword value)

theorem keyword_ne_invariant (value : HardKeyword) (context : ParseContext)
    (input : State) (error : ParserInvariantError) :
    keyword value context input ≠ .invariant error :=
  (keyword_ordinary value context).ne_invariant input error

theorem symbol_ordinary (value : Symbol) (context : ParseContext) :
    Parser.Ordinary (symbol value context) :=
  acceptToken_ordinary (.symbol value) context (· == .symbol value)

theorem symbol_ne_invariant (value : Symbol) (context : ParseContext)
    (input : State) (error : ParserInvariantError) :
    symbol value context input ≠ .invariant error :=
  (symbol_ordinary value context).ne_invariant input error

theorem contextual_ordinary (value : ContextualKeyword)
    (context : ParseContext) :
    Parser.Ordinary (contextual value context) :=
  acceptToken_ordinary (.contextual value) context (·.isContextual value)

theorem contextual_ne_invariant (value : ContextualKeyword)
    (context : ParseContext) (input : State) (error : ParserInvariantError) :
    contextual value context input ≠ .invariant error :=
  (contextual_ordinary value context).ne_invariant input error

/-- Raw ordinary-identifier recognition is ordinary on every input. -/
theorem rawIdentifier_ordinary (context : ParseContext) :
    Parser.Ordinary (rawIdentifier context) := by
  intro input
  cases result : rawIdentifier context input with
  | ok name next => exact Or.inl ⟨name, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      unfold rawIdentifier at result
      cases found : input.peek? with
      | none => simp [found, rejectAt] at result
      | some token =>
          rcases token with ⟨span, kind⟩
          cases kind <;> simp [found, rejectAt] at result

theorem rawIdentifier_ne_invariant (context : ParseContext)
    (input : State) (error : ParserInvariantError) :
    rawIdentifier context input ≠ .invariant error :=
  (rawIdentifier_ordinary context).ne_invariant input error

/-- Checked identifiers retain ordinary control flow through diagnostics. -/
theorem identifier_ordinary (context : ParseContext) :
    Parser.Ordinary (identifier context) := by
  intro input
  cases result : identifier context input with
  | ok name next => exact Or.inl ⟨name, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      unfold identifier at result
      cases rawResult : rawIdentifier context input with
      | invariant rawError =>
          exact False.elim
            (rawIdentifier_ne_invariant context input rawError rawResult)
      | reject failure rejected => simp [rawResult] at result
      | ok name next =>
          simp only [rawResult] at result
          split at result <;> contradiction

theorem identifier_ne_invariant (context : ParseContext)
    (input : State) (error : ParserInvariantError) :
    identifier context input ≠ .invariant error :=
  (identifier_ordinary context).ne_invariant input error

private theorem identifier_cursor_lt_onSuccess (context : ParseContext)
    {input next : State} {name : Identifier}
    (result : identifier context input = .ok name next) :
    input.cursor < next.cursor := by
  rw [(identifier_ok_state_shape context result).choose_spec.2.2.2]
  simp

/-- Generic token acceptance can serve as a strict delimited element parser. -/
theorem acceptToken_elementTotalityContract
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) :
    ElementTotalityContract (acceptToken expected context accepts) := {
  validFor := (acceptToken_validFor expected context accepts).mono
    (fun _ _ _ => trivial)
  preservesTokenWindow :=
    acceptToken_preservesTokenWindow expected context accepts
  cursorLtOnSuccess :=
    acceptToken_cursor_lt_onSuccess expected context accepts
  invariantFree := fun input _ error =>
    acceptToken_ne_invariant expected context accepts input error
}

theorem keyword_elementTotalityContract
    (value : HardKeyword) (context : ParseContext) :
    ElementTotalityContract (keyword value context) :=
  acceptToken_elementTotalityContract (.keyword value) context
    (· == .keyword value)

theorem symbol_elementTotalityContract
    (value : Symbol) (context : ParseContext) :
    ElementTotalityContract (symbol value context) :=
  acceptToken_elementTotalityContract (.symbol value) context
    (· == .symbol value)

theorem contextual_elementTotalityContract
    (value : ContextualKeyword) (context : ParseContext) :
    ElementTotalityContract (contextual value context) :=
  acceptToken_elementTotalityContract (.contextual value) context
    (·.isContextual value)

/-- Canonical identifiers can instantiate every generic delimited loop. -/
theorem identifier_elementTotalityContract (context : ParseContext) :
    ElementTotalityContract (identifier context) := {
  validFor := (identifier_validFor context).mono (fun _ _ _ => trivial)
  preservesTokenWindow := identifier_preservesTokenWindow context
  cursorLtOnSuccess := identifier_cursor_lt_onSuccess context
  invariantFree := fun input _ error =>
    identifier_ne_invariant context input error
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
/-! Element-fuel-aware totality for recursive delimited parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
The element contract needed when invariant freedom holds only below a fixed
recursive-fuel bound. This is weaker than `ElementTotalityContract`: finite
recursive parsers need not be invariant-free on every valid state.
-/
structure FuelElementTotalityContract {α : Type}
    (element : Parser α) (fuel : Nat) : Prop where
  validFor : element.ValidFor (fun _ _ => True)
  preservesTokenWindow : Parser.PreservesTokenWindow element
  cursorLtOnSuccess : ∀ {input next : State} {value : α},
    element input = .ok value next → input.cursor < next.cursor
  ordinary : ∀ input, input.ValidFor → input.remainingCount < fuel →
    (∃ value next, element input = .ok value next) ∨
      (∃ failure next, element input = .reject failure next)

namespace FuelElementTotalityContract

/-- A contract at a larger fuel bound also proves every smaller bound. -/
theorem weaken {α : Type} {element : Parser α}
    {smallFuel largeFuel : Nat}
    (contract : FuelElementTotalityContract element largeFuel)
    (bound : smallFuel ≤ largeFuel) :
    FuelElementTotalityContract element smallFuel := {
  validFor := contract.validFor
  preservesTokenWindow := contract.preservesTokenWindow
  cursorLtOnSuccess := contract.cursorLtOnSuccess
  ordinary := fun input inputValid adequate =>
    contract.ordinary input inputValid
      (Nat.lt_of_lt_of_le adequate bound)
}

theorem ne_invariant {α : Type} {element : Parser α} {fuel : Nat}
    (contract : FuelElementTotalityContract element fuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    element input ≠ .invariant error := by
  intro failed
  rcases contract.ordinary input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end FuelElementTotalityContract

private theorem closeDelimited_ordinary_variant {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) :
    Parser.Ordinary (closeDelimited opening closing context elementsRev) := by
  intro input
  rcases symbol_ordinary closing context input with
    ⟨token, next, result⟩ | ⟨failure, next, result⟩
  · exact Or.inl ⟨{
        span := SourceSpan.cover opening.span token.span
        elements := elementsRev.reverse
      }, next, by unfold closeDelimited; simp only [result]⟩
  · exact Or.inr ⟨failure, next, by
      unfold closeDelimited
      simp only [result]⟩

/-- Cursor-monotone steps in one token window preserve a remaining-count bound. -/
theorem remainingCount_lt_of_cursor_le
    {input next : State} {fuel : Nat}
    (windowEq : next.window = input.window)
    (cursorLe : input.cursor ≤ next.cursor)
    (adequate : input.remainingCount < fuel) :
    next.remainingCount < fuel := by
  have endIndexEq : next.window.endIndex = input.window.endIndex :=
    congrArg TokenWindow.endIndex windowEq
  simp only [State.remainingCount] at adequate ⊢
  rw [endIndexEq]
  omega

/-- One strict cursor step spends one unit of a remaining-count fuel bound. -/
theorem remainingCount_lt_after_strict_progress
    {input next : State} {fuel : Nat}
    (nextValid : next.ValidFor) (windowEq : next.window = input.window)
    (progress : input.cursor < next.cursor)
    (adequate : input.remainingCount < fuel + 1) :
    next.remainingCount < fuel := by
  have nextCursorBound : next.cursor ≤ input.window.endIndex := by
    simpa [windowEq] using nextValid.cursor_le_endIndex
  have endIndexEq : next.window.endIndex = input.window.endIndex :=
    congrArg TokenWindow.endIndex windowEq
  simp only [State.remainingCount] at adequate ⊢
  rw [endIndexEq]
  omega

/--
The delimited tail loop remains ordinary when every element state is below the
fixed recursive-fuel bound, independently of the loop's own decreasing fuel.
-/
theorem afterDelimitedElement_ordinary_of_elementFuel {α : Type}
    (element : Parser α) (elementFuel : Nat)
    (contract : FuelElementTotalityContract element elementFuel)
    (closing : Symbol) (allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ loopFuel elementsRev input,
      input.ValidFor → input.remainingCount < loopFuel →
      input.remainingCount < elementFuel →
      (∃ values next,
        afterDelimitedElement element closing allowTrailing context phase
          opening loopFuel elementsRev input = .ok values next) ∨
      (∃ failure next,
        afterDelimitedElement element closing allowTrailing context phase
          opening loopFuel elementsRev input = .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro elementsRev input inputValid loopAdequate elementAdequate
      omega
  | succ loopFuel inductionHypothesis =>
      intro elementsRev input inputValid loopAdequate elementAdequate
      unfold afterDelimitedElement
      split
      · cases commaResult : symbol .comma context input with
        | invariant error =>
            exact False.elim
              (symbol_ne_invariant .comma context input error commaResult)
        | reject failure rejected =>
            exact Or.inr ⟨failure, rejected, rfl⟩
        | ok comma afterComma =>
            have commaValid := symbol_validFor .comma context input inputValid
            rw [commaResult] at commaValid
            have commaWindow := symbol_preservesTokenWindow .comma context input
            rw [commaResult] at commaWindow
            have commaProgress : input.cursor < afterComma.cursor :=
              acceptToken_cursor_lt_onSuccess (.symbol .comma) context
                (· == .symbol .comma) commaResult
            have afterCommaAdequate :
                afterComma.remainingCount < elementFuel :=
              remainingCount_lt_after_strict_progress commaValid.2.1
                commaWindow.2 commaProgress (by omega)
            dsimp only
            split
            · exact closeDelimited_ordinary_variant opening closing context elementsRev
                afterComma
            · cases elementResult : element afterComma with
              | invariant error =>
                  exact False.elim (contract.ne_invariant afterComma
                    commaValid.2.1 afterCommaAdequate error elementResult)
              | reject failure rejected =>
                  exact Or.inr ⟨failure, rejected, rfl⟩
              | ok value next =>
                  have valueValid := contract.validFor afterComma commaValid.2.1
                  rw [elementResult] at valueValid
                  have valueWindow := contract.preservesTokenWindow afterComma
                  rw [elementResult] at valueWindow
                  have valueProgress := contract.cursorLtOnSuccess elementResult
                  dsimp only
                  split
                  · have nextWindow : next.window = input.window :=
                      valueWindow.2.trans commaWindow.2
                    have nextLoopAdequate :
                        next.remainingCount < loopFuel :=
                      remainingCount_lt_after_strict_progress valueValid.2.1
                        nextWindow (Nat.lt_trans commaProgress valueProgress)
                        loopAdequate
                    have nextElementAdequate :
                        next.remainingCount < elementFuel :=
                      remainingCount_lt_after_strict_progress valueValid.2.1
                        valueWindow.2 valueProgress (by omega)
                    exact inductionHypothesis (value :: elementsRev) next
                      valueValid.2.1 nextLoopAdequate nextElementAdequate
                  · omega
      · split
        · exact closeDelimited_ordinary_variant opening closing context elementsRev input
        · exact Or.inr ⟨_, input, rfl⟩

/--
One extra unit of recursive fuel at the delimited input pays for the opening
delimiter, after which every element call satisfies the fixed fuel bound.
-/
theorem delimitedWithPolicy_ordinary_of_elementFuel {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (elementFuel : Nat)
    (contract : FuelElementTotalityContract element elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1) :
    (∃ values next,
      delimitedWithPolicy opening closing allowEmpty allowTrailing element
        context phase input = .ok values next) ∨
    (∃ failure next,
      delimitedWithPolicy opening closing allowEmpty allowTrailing element
        context phase input = .reject failure next) := by
  unfold delimitedWithPolicy
  cases openingResult : symbol opening context input with
  | invariant error =>
      exact False.elim
        (symbol_ne_invariant opening context input error openingResult)
  | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
  | ok openingToken afterOpening =>
      have openingValid := symbol_validFor opening context input inputValid
      rw [openingResult] at openingValid
      have openingWindow := symbol_preservesTokenWindow opening context input
      rw [openingResult] at openingWindow
      have openingProgress : input.cursor < afterOpening.cursor :=
        acceptToken_cursor_lt_onSuccess (.symbol opening) context
          (· == .symbol opening) openingResult
      have afterOpeningAdequate :
          afterOpening.remainingCount < elementFuel :=
        remainingCount_lt_after_strict_progress openingValid.2.1
          openingWindow.2 openingProgress adequate
      dsimp only
      split
      · exact closeDelimited_ordinary_variant openingToken closing context []
          afterOpening
      · cases elementResult : element afterOpening with
        | invariant error =>
            exact False.elim (contract.ne_invariant afterOpening
              openingValid.2.1 afterOpeningAdequate error elementResult)
        | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
        | ok value next =>
            have valueValid := contract.validFor afterOpening openingValid.2.1
            rw [elementResult] at valueValid
            have valueWindow := contract.preservesTokenWindow afterOpening
            rw [elementResult] at valueWindow
            have valueProgress := contract.cursorLtOnSuccess elementResult
            dsimp only
            split
            · have nextLoopAdequate :
                  next.remainingCount < afterOpening.remainingCount + 1 :=
                remainingCount_lt_after_strict_progress valueValid.2.1
                  valueWindow.2 valueProgress (by omega)
              have nextElementAdequate :
                  next.remainingCount < elementFuel :=
                remainingCount_lt_after_strict_progress valueValid.2.1
                  valueWindow.2 valueProgress (by omega)
              exact afterDelimitedElement_ordinary_of_elementFuel element
                elementFuel contract closing allowTrailing context phase
                openingToken (afterOpening.remainingCount + 1) [value] next
                valueValid.2.1 nextLoopAdequate nextElementAdequate
            · omega

/-- Fuel-aware totality for the ordinary trailing-comma wrapper. -/
theorem delimited_ordinary_of_elementFuel {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (elementFuel : Nat)
    (contract : FuelElementTotalityContract element elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1) :
    (∃ values next,
      delimited opening closing allowEmpty element context phase input =
        .ok values next) ∨
    (∃ failure next,
      delimited opening closing allowEmpty element context phase input =
        .reject failure next) :=
  delimitedWithPolicy_ordinary_of_elementFuel opening closing allowEmpty true
    element context phase elementFuel contract input inputValid adequate

theorem delimited_ne_invariant_of_elementFuel {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (elementFuel : Nat)
    (contract : FuelElementTotalityContract element elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    delimited opening closing allowEmpty element context phase input ≠
      .invariant error := by
  intro failed
  rcases delimited_ordinary_of_elementFuel opening closing allowEmpty element
      context phase elementFuel contract input inputValid adequate with
    ⟨values, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser
end
