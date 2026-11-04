import Solcore.Syntax.Parser.Tokens
import Solcore.Syntax.Parser.Primitive
import Solcore.Syntax.ValidityBasics
import Solcore.Syntax.Parser.State
import Solcore.Syntax.Grammar.Basics

/-!
Basic proofs about parser primitives, names, literals and delimited lists.
`Parser/Signatures` and `Parser/Blocks` keep theorems beside private helpers and those
theorems need this file, so production code imports it. Keep it small.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.PrimitiveProperties
/-! Provenance and state-preservation laws for primitive token consumers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem advanceAfterPeek_validFor {state : State} {token : Token}
    (valid : state.ValidFor) (found : state.peek? = some token) :
    token.span.ValidFor state.file ∧
      ({ state with cursor := state.cursor + 1 } : State).ValidFor ∧
      ({ state with cursor := state.cursor + 1 } : State).file = state.file := by
  refine ⟨valid.peek?_span_validFor found, ?_, rfl⟩
  apply valid.advance?_validFor (token := token)
  unfold State.advance?
  rw [found]
  rfl

/-- `rejectAt` retains a valid state and uses its valid current span. -/
theorem rejectAt_reject_validFor {α : Type} {state next : State}
    {failure : Failure} (valid : state.ValidFor)
    (expected : NonemptyList ParseExpectation) (context : ParseContext)
    (result : rejectAt (α := α) state expected context =
      .reject failure next) :
    failure.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold rejectAt at result
  cases result
  exact ⟨valid.currentSpan_validFor, valid, rfl⟩

/-- Accepted tokens have valid spans and advance to a valid state. -/
theorem acceptToken_ok_validFor {state next : State} {token : Token}
    (valid : state.ValidFor) (expected : ParseExpectation)
    (context : ParseContext) (accepts : TokenKind → Bool)
    (result : acceptToken expected context accepts state = .ok token next) :
    token.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold acceptToken at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some current =>
      simp only [found] at result
      split at result
      · cases result
        exact advanceAfterPeek_validFor valid found
      · unfold rejectAt at result
        contradiction

/-- Successful token acceptance returns the current token and increments only the cursor. -/
theorem acceptToken_ok_state_shape {state next : State} {token : Token}
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool)
    (result : acceptToken expected context accepts state = .ok token next) :
    state.peek? = some token ∧ next = { state with cursor := state.cursor + 1 } := by
  unfold acceptToken at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some current =>
      simp only [found] at result
      split at result
      · cases result
        exact ⟨rfl, rfl⟩
      · unfold rejectAt at result
        contradiction

/-- Successful symbol parsing has the generic token-consumer state shape. -/
theorem symbol_ok_state_shape {state next : State} {token : Token}
    (value : Symbol) (context : ParseContext)
    (result : symbol value context state = .ok token next) :
    state.peek? = some token ∧ next = { state with cursor := state.cursor + 1 } := by
  exact acceptToken_ok_state_shape (.symbol value) context
    (· == .symbol value) result

/-- Rejected token acceptance retains a valid failure span and state. -/
theorem acceptToken_reject_validFor {state next : State}
    {failure : Failure} (valid : state.ValidFor)
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool)
    (result : acceptToken expected context accepts state =
      .reject failure next) :
    failure.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold acceptToken at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_reject_validFor valid _ _ result
  | some current =>
      simp only [found] at result
      split at result
      · contradiction
      · exact rejectAt_reject_validFor valid _ _ result

/-- Raw ordinary identifiers preserve span provenance and state validity. -/
theorem rawIdentifier_ok_validFor {state next : State} {name : Identifier}
    (valid : state.ValidFor) (context : ParseContext)
    (result : rawIdentifier context state = .ok name next) :
    name.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold rawIdentifier at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case identifier text =>
        cases result
        exact advanceAfterPeek_validFor valid found

/-- Raw ordinary-identifier rejection preserves failure provenance and state. -/
theorem rawIdentifier_reject_validFor {state next : State}
    {failure : Failure} (valid : state.ValidFor) (context : ParseContext)
    (result : rawIdentifier context state = .reject failure next) :
    failure.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold rawIdentifier at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_reject_validFor valid _ _ result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { exact rejectAt_reject_validFor valid _ _ result }
      contradiction

/-- Canonical identifier acceptance, including hyphen reporting, is valid. -/
theorem identifier_ok_validFor {state next : State} {name : Identifier}
    (valid : state.ValidFor) (context : ParseContext)
    (result : identifier context state = .ok name next) :
    name.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  cases raw : rawIdentifier context state with
  | invariant error =>
      simp only [identifier, raw] at result
      contradiction
  | reject failure rejected =>
      simp only [identifier, raw] at result
      contradiction
  | ok parsed afterName =>
      simp only [identifier, raw] at result
      have parsedValid := rawIdentifier_ok_validFor valid context raw
      split at result
      · cases result
        refine ⟨parsedValid.1, ?_, parsedValid.2.2⟩
        apply parsedValid.2.1.emit_validFor
        simpa [parsedValid.2.2] using parsedValid.1
      · cases result
        exact parsedValid

/-- Successful identifier parsing exposes its input token and cursor advance. -/
theorem identifier_ok_state_shape {state next : State} {name : Identifier}
    (context : ParseContext)
    (result : identifier context state = .ok name next) :
    ∃ token,
      state.peek? = some token ∧
        token.span = name.span ∧
        next.tokens = state.tokens ∧
        next.cursor = state.cursor + 1 := by
  cases raw : rawIdentifier context state with
  | invariant error =>
      simp only [identifier, raw] at result
      contradiction
  | reject failure rejected =>
      simp only [identifier, raw] at result
      contradiction
  | ok parsed afterName =>
      simp only [identifier, raw] at result
      have rawShape : ∃ token,
          state.peek? = some token ∧
            token.span = parsed.span ∧
            afterName.tokens = state.tokens ∧
            afterName.cursor = state.cursor + 1 := by
        unfold rawIdentifier at raw
        cases found : state.peek? with
        | none =>
            simp only [found] at raw
            unfold rejectAt at raw
            contradiction
        | some token =>
            rcases token with ⟨span, kind⟩
            cases kind <;> simp only [found] at raw
            all_goals try { unfold rejectAt at raw; contradiction }
            case identifier text =>
              cases raw
              exact ⟨_, rfl, rfl, rfl, rfl⟩
      rcases rawShape with
        ⟨token, tokenFound, tokenSpan, tokensEq, cursorEq⟩
      split at result
      · cases result
        exact ⟨token, tokenFound, tokenSpan, tokensEq, cursorEq⟩
      · cases result
        exact ⟨token, tokenFound, tokenSpan, tokensEq, cursorEq⟩

/-- Canonical identifier rejection is exactly valid raw rejection. -/
theorem identifier_reject_validFor {state next : State}
    {failure : Failure} (valid : state.ValidFor) (context : ParseContext)
    (result : identifier context state = .reject failure next) :
    failure.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  cases raw : rawIdentifier context state with
  | invariant error =>
      simp only [identifier, raw] at result
      contradiction
  | ok name afterName =>
      simp only [identifier, raw] at result
      split at result <;> contradiction
  | reject rejected rejectedState =>
      simp only [identifier, raw] at result
      cases result
      exact rawIdentifier_reject_validFor valid context raw

/-- Yul identifiers preserve span provenance and state validity. -/
theorem yulIdentifier_ok_validFor {state next : State} {name : Identifier}
    (valid : state.ValidFor) (context : ParseContext)
    (result : yulIdentifier context state = .ok name next) :
    name.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold yulIdentifier at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case yulIdentifier text =>
        cases result
        exact advanceAfterPeek_validFor valid found

/-- Yul-identifier rejection preserves failure provenance and state. -/
theorem yulIdentifier_reject_validFor {state next : State}
    {failure : Failure} (valid : state.ValidFor) (context : ParseContext)
    (result : yulIdentifier context state = .reject failure next) :
    failure.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold yulIdentifier at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_reject_validFor valid _ _ result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { exact rejectAt_reject_validFor valid _ _ result }
      contradiction

/-- Core literal acceptance preserves its located span and state validity. -/
theorem coreLiteral_ok_validFor {state next : State} {literal : CoreLiteral}
    (valid : state.ValidFor)
    (result : coreLiteral state = .ok literal next) :
    literal.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold coreLiteral at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      all_goals cases result
      all_goals exact advanceAfterPeek_validFor valid found

/-- Core literal rejection preserves failure provenance and state validity. -/
theorem coreLiteral_reject_validFor {state next : State}
    {failure : Failure} (valid : state.ValidFor)
    (result : coreLiteral state = .reject failure next) :
    failure.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold coreLiteral at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_reject_validFor valid _ _ result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { exact rejectAt_reject_validFor valid _ _ result }
      all_goals contradiction

/-- Boolean builtin acceptance preserves its located span and state validity. -/
theorem booleanIdentifier_ok_validFor {state next : State}
    {name : Identifier} (valid : state.ValidFor)
    (result : booleanIdentifier state = .ok name next) :
    name.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold booleanIdentifier at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        all_goals cases result
        all_goals exact advanceAfterPeek_validFor valid found

/-- Boolean builtin rejection preserves failure provenance and state validity. -/
theorem booleanIdentifier_reject_validFor {state next : State}
    {failure : Failure} (valid : state.ValidFor)
    (result : booleanIdentifier state = .reject failure next) :
    failure.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold booleanIdentifier at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_reject_validFor valid _ _ result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { exact rejectAt_reject_validFor valid _ _ result }
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { exact rejectAt_reject_validFor valid _ _ result }
        all_goals contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Validity
/-! Compositional validity contracts for canonical parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace Located

/-- A located value has source provenance valid for the supplied file. -/
def ValidFor {α : Type} (file : SourceFile) (value : Located α) : Prop :=
  value.span.ValidFor file

end Located

namespace Parser

namespace Reply

/--
Every ordinary reply retains the immutable token array and active token
window of its input. Invariant failures carry no parser state.
-/
def PreservesTokenWindow {α : Type} (reply : Reply α)
    (input : State) : Prop :=
  match reply with
  | .ok _ next
  | .reject _ next =>
      next.tokens = input.tokens ∧ next.window = input.window
  | .invariant _ => True

namespace PreservesTokenWindow

/-- Retarget an ordinary reply through an equal immutable token window. -/
theorem trans {α : Type} {reply : Reply α} {middle input : State}
    (replyShape : reply.PreservesTokenWindow middle)
    (middleShape : middle.tokens = input.tokens ∧
      middle.window = input.window) :
    reply.PreservesTokenWindow input := by
  cases reply with
  | ok value next =>
      exact ⟨replyShape.1.trans middleShape.1,
        replyShape.2.trans middleShape.2⟩
  | reject failure next =>
      exact ⟨replyShape.1.trans middleShape.1,
        replyShape.2.trans middleShape.2⟩
  | invariant error => trivial

end PreservesTokenWindow

/--
Ordinary parser results preserve source provenance and state validity.
Invariant failures remain admissible because they are outside source-result
semantics and are handled by the total public parser boundary.
-/
def ValidFor {α : Type} (reply : Reply α) (input : State)
    (valueValid : SourceFile → α → Prop) : Prop :=
  match reply with
  | .ok value next =>
      valueValid input.file value ∧ next.ValidFor ∧
        next.file = input.file
  | .reject failure next =>
      failure.span.ValidFor input.file ∧ next.ValidFor ∧
        next.file = input.file
  | .invariant _ => True

namespace ValidFor

/-- Change only the presentation of an input file known to be equal. -/
theorem of_file_eq {α : Type} {reply : Reply α} {input other : State}
    {valueValid : SourceFile → α → Prop}
    (valid : reply.ValidFor input valueValid)
    (fileEq : input.file = other.file) :
    reply.ValidFor other valueValid := by
  cases reply <;> simp [Reply.ValidFor, fileEq] at valid ⊢ <;>
    exact valid

/-- Transport only the successful value predicate of a reply contract. -/
theorem mono {α : Type} {reply : Reply α} {input : State}
    {first second : SourceFile → α → Prop}
    (valid : reply.ValidFor input first)
    (implies : ∀ file value, first file value → second file value) :
    reply.ValidFor input second := by
  cases reply with
  | ok value next =>
      exact ⟨implies input.file value valid.1, valid.2.1, valid.2.2⟩
  | reject failure next => exact valid
  | invariant error => trivial

end ValidFor

end Reply

namespace Parser

/-- A parser satisfies its result contract for every valid input state. -/
def ValidFor {α : Type} (parser : Parser α)
    (valueValid : SourceFile → α → Prop) : Prop :=
  ∀ input, input.ValidFor → (parser input).ValidFor input valueValid

/-- Every ordinary result preserves the input token array and window. -/
def PreservesTokenWindow {α : Type} (parser : Parser α) : Prop :=
  ∀ input, (parser input).PreservesTokenWindow input

/-- Successful parsing preserves the immutable token carrier. -/
def PreservesTokensOnSuccess {α : Type} (parser : Parser α) : Prop :=
  ∀ input value next, parser input = .ok value next →
    next.tokens = input.tokens

/-- Successful parsing never moves the cursor backwards. -/
def CursorMonotoneOnSuccess {α : Type} (parser : Parser α) : Prop :=
  ∀ input value next, parser input = .ok value next →
    input.cursor ≤ next.cursor

/--
A successful located parser starts its result at the current input token.
Requiring the token itself, rather than only `currentSpan`, excludes a
spurious success at the end of an input window.
-/
def StartsAtCurrentTokenOnSuccess {α : Type} (parser : Parser α)
    (spanOf : α → SourceSpan) : Prop :=
  ∀ input value next, parser input = .ok value next →
    ∃ token, input.peek? = some token ∧
      token.span.startByte = (spanOf value).startByte

/-- The stronger ordinary-result contract implies success-only preservation. -/
theorem PreservesTokenWindow.preservesTokensOnSuccess
    {α : Type} {parser : Parser α}
    (preserves : PreservesTokenWindow parser) :
    PreservesTokensOnSuccess parser := by
  intro input value next parsed
  have result := preserves input
  rw [parsed] at result
  exact result.1

/-- A pure parser retains the complete immutable token window. -/
theorem pure_preservesTokenWindow {α : Type} (value : α) :
    PreservesTokenWindow (pure value : Parser α) := by
  intro input
  exact ⟨rfl, rfl⟩

/-- Sequential composition preserves a shared ordinary-result contract. -/
theorem bind_preservesTokenWindow {α β : Type} {first : Parser α}
    {next : α → Parser β}
    (firstPreserves : PreservesTokenWindow first)
    (nextPreserves : ∀ value, PreservesTokenWindow (next value)) :
    PreservesTokenWindow (first >>= next) := by
  intro input
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error).PreservesTokenWindow input
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      have firstShape := firstPreserves input
      rw [firstResult] at firstShape
      cases nextResult : next firstValue afterFirst with
      | ok value final =>
          have nextShape := nextPreserves firstValue afterFirst
          rw [nextResult] at nextShape
          simp only [nextResult, Reply.PreservesTokenWindow]
          exact ⟨nextShape.1.trans firstShape.1,
            nextShape.2.trans firstShape.2⟩
      | reject failure rejected =>
          have nextShape := nextPreserves firstValue afterFirst
          rw [nextResult] at nextShape
          simp only [nextResult, Reply.PreservesTokenWindow]
          exact ⟨nextShape.1.trans firstShape.1,
            nextShape.2.trans firstShape.2⟩
      | invariant error =>
          simp only [nextResult, Reply.PreservesTokenWindow]
  | reject failure rejected =>
      have firstShape := firstPreserves input
      rw [firstResult] at firstShape
      simpa only [Reply.PreservesTokenWindow] using firstShape
  | invariant error => simp only [Reply.PreservesTokenWindow]

/-- Transactional ordered choice preserves a shared token-window contract. -/
theorem orElse_preservesTokenWindow {α : Type}
    {first second : Parser α}
    (firstPreserves : PreservesTokenWindow first)
    (secondPreserves : PreservesTokenWindow second) :
    PreservesTokenWindow (orElse first second) := by
  intro input
  unfold orElse
  cases firstResult : first input with
  | ok value next =>
      have firstShape := firstPreserves input
      rw [firstResult] at firstShape
      simpa only [Reply.PreservesTokenWindow] using firstShape
  | reject failure rejected => exact secondPreserves input
  | invariant error => simp only [Reply.PreservesTokenWindow]

/-- A pure parser leaves the token carrier unchanged. -/
theorem pure_preservesTokensOnSuccess {α : Type} (value : α) :
    PreservesTokensOnSuccess (pure value : Parser α) := by
  intro input result next parsed
  cases parsed
  rfl

/-- A pure parser leaves the cursor in place. -/
theorem pure_cursorMonotoneOnSuccess {α : Type} (value : α) :
    CursorMonotoneOnSuccess (pure value : Parser α) := by
  intro input result next parsed
  cases parsed
  exact Nat.le_refl _

/-- Sequential composition preserves the carrier when both stages do. -/
theorem bind_preservesTokensOnSuccess {α β : Type} {first : Parser α}
    {next : α → Parser β}
    (firstPreserves : PreservesTokensOnSuccess first)
    (nextPreserves : ∀ value, PreservesTokensOnSuccess (next value)) :
    PreservesTokensOnSuccess (first >>= next) := by
  intro input value final parsed
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      simp only [firstResult] at parsed
      exact (nextPreserves firstValue afterFirst value final parsed).trans
        (firstPreserves input firstValue afterFirst firstResult)
  | reject failure rejected =>
      simp only [firstResult] at parsed
      cases parsed
  | invariant error =>
      simp only [firstResult] at parsed
      cases parsed

/-- Sequential composition is monotone when both stages are monotone. -/
theorem bind_cursorMonotoneOnSuccess {α β : Type} {first : Parser α}
    {next : α → Parser β}
    (firstMonotone : CursorMonotoneOnSuccess first)
    (nextMonotone : ∀ value, CursorMonotoneOnSuccess (next value)) :
    CursorMonotoneOnSuccess (first >>= next) := by
  intro input value final parsed
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      simp only [firstResult] at parsed
      exact Nat.le_trans (firstMonotone input firstValue afterFirst firstResult)
        (nextMonotone firstValue afterFirst value final parsed)
  | reject failure rejected =>
      simp only [firstResult] at parsed
      cases parsed
  | invariant error =>
      simp only [firstResult] at parsed
      cases parsed

/--
A bind starts with its first parser when every successful continuation keeps
the first value's starting byte. This is the common shape of parsers that
construct an outer covering span from a leading marker.
-/
theorem bind_startsAtCurrentTokenOnSuccess_of_first
    {α β : Type} {first : Parser α} {next : α → Parser β}
    {firstSpan : α → SourceSpan} {resultSpan : β → SourceSpan}
    (firstStarts : StartsAtCurrentTokenOnSuccess first firstSpan)
    (continuationKeepsStart : ∀ firstValue input value final,
      next firstValue input = .ok value final →
      (firstSpan firstValue).startByte = (resultSpan value).startByte) :
    StartsAtCurrentTokenOnSuccess (first >>= next) resultSpan := by
  intro input value final parsed
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      simp only [firstResult] at parsed
      rcases firstStarts input firstValue afterFirst firstResult with
        ⟨token, found, firstStart⟩
      exact ⟨token, found,
        firstStart.trans (continuationKeepsStart _ _ _ _ parsed)⟩
  | reject failure rejected =>
      simp only [firstResult] at parsed
      cases parsed
  | invariant error =>
      simp only [firstResult] at parsed
      cases parsed

/-- Transactional ordered choice preserves a shared carrier contract. -/
theorem orElse_preservesTokensOnSuccess {α : Type}
    {first second : Parser α}
    (firstPreserves : PreservesTokensOnSuccess first)
    (secondPreserves : PreservesTokensOnSuccess second) :
    PreservesTokensOnSuccess (orElse first second) := by
  intro input value next parsed
  unfold orElse at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      simp only [firstResult] at parsed
      have preserved :=
        firstPreserves input firstValue afterFirst firstResult
      cases parsed
      exact preserved
  | reject failure rejected =>
      simp only [firstResult] at parsed
      exact secondPreserves input value next parsed
  | invariant error =>
      simp only [firstResult] at parsed
      cases parsed

/-- Transactional ordered choice preserves cursor monotonicity. -/
theorem orElse_cursorMonotoneOnSuccess {α : Type}
    {first second : Parser α}
    (firstMonotone : CursorMonotoneOnSuccess first)
    (secondMonotone : CursorMonotoneOnSuccess second) :
    CursorMonotoneOnSuccess (orElse first second) := by
  intro input value next parsed
  unfold orElse at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      simp only [firstResult] at parsed
      have monotone := firstMonotone input firstValue afterFirst firstResult
      cases parsed
      exact monotone
  | reject failure rejected =>
      simp only [firstResult] at parsed
      exact secondMonotone input value next parsed
  | invariant error =>
      simp only [firstResult] at parsed
      cases parsed

/-- Transactional ordered choice preserves a shared result-start contract. -/
theorem orElse_startsAtCurrentTokenOnSuccess {α : Type}
    {first second : Parser α} {spanOf : α → SourceSpan}
    (firstStarts : StartsAtCurrentTokenOnSuccess first spanOf)
    (secondStarts : StartsAtCurrentTokenOnSuccess second spanOf) :
    StartsAtCurrentTokenOnSuccess (orElse first second) spanOf := by
  intro input value next parsed
  unfold orElse at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      simp only [firstResult] at parsed
      have starts := firstStarts input firstValue afterFirst firstResult
      cases parsed
      exact starts
  | reject failure rejected =>
      simp only [firstResult] at parsed
      exact secondStarts input value next parsed
  | invariant error =>
      simp only [firstResult] at parsed
      cases parsed

/-- Build a parser contract from its ordinary success and rejection branches. -/
theorem validFor_of_ok_reject {α : Type} (parser : Parser α)
    (valueValid : SourceFile → α → Prop)
    (okValid : ∀ input, input.ValidFor → ∀ value next,
      parser input = .ok value next →
      valueValid input.file value ∧ next.ValidFor ∧
        next.file = input.file)
    (rejectValid : ∀ input, input.ValidFor → ∀ failure next,
      parser input = .reject failure next →
      failure.span.ValidFor input.file ∧ next.ValidFor ∧
        next.file = input.file) :
    parser.ValidFor valueValid := by
  intro input inputValid
  cases result : parser input with
  | ok value next => exact okValid input inputValid value next result
  | reject failure next =>
      exact rejectValid input inputValid failure next result
  | invariant error => trivial

/-- Pure parsers preserve a valid input state. -/
theorem pure_validFor {α : Type} (value : α)
    (valueValid : SourceFile → α → Prop)
    (validValue : ∀ file, valueValid file value) :
    (pure value : Parser α).ValidFor valueValid := by
  intro input inputValid
  exact ⟨validValue input.file, inputValid, rfl⟩

/--
Sequential composition may use the first value's validity evidence when
establishing the continuation at the actual intermediate state.
-/
theorem bind_validFor_of_value {α β : Type} {first : Parser α}
    {next : α → Parser β}
    {firstValueValid : SourceFile → α → Prop}
    {resultValid : SourceFile → β → Prop}
    (firstValid : first.ValidFor firstValueValid)
    (nextValid : ∀ value input, input.ValidFor →
      firstValueValid input.file value →
      (next value input).ValidFor input resultValid) :
    (first >>= next).ValidFor resultValid := by
  intro input inputValid
  have firstResult := firstValid input inputValid
  have binding : (first >>= next) input =
      match first input with
      | .ok value afterFirst => next value afterFirst
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
    rfl
  cases result : first input with
  | ok value afterFirst =>
      rw [result] at firstResult
      rw [binding, result]
      have valueValidAfter : firstValueValid afterFirst.file value := by
        simpa [firstResult.2.2] using firstResult.1
      exact (nextValid value afterFirst firstResult.2.1
        valueValidAfter).of_file_eq firstResult.2.2
  | reject failure rejected =>
      rw [result] at firstResult
      rw [binding, result]
      exact firstResult
  | invariant error =>
      rw [binding, result]
      trivial

/-- Sequential composition preserves the continuation's result contract. -/
theorem bind_validFor {α β : Type} {first : Parser α}
    {next : α → Parser β}
    {firstValueValid : SourceFile → α → Prop}
    {resultValid : SourceFile → β → Prop}
    (firstValid : first.ValidFor firstValueValid)
    (nextValid : ∀ value, (next value).ValidFor resultValid) :
    (first >>= next).ValidFor resultValid := by
  apply bind_validFor_of_value firstValid
  intro value input inputValid _valueValid
  exact nextValid value input inputValid

/-- Transactional ordered choice preserves a shared result contract. -/
theorem orElse_validFor {α : Type} {first second : Parser α}
    {valueValid : SourceFile → α → Prop}
    (firstValid : first.ValidFor valueValid)
    (secondValid : second.ValidFor valueValid) :
    (orElse first second).ValidFor valueValid := by
  intro input inputValid
  have firstResult := firstValid input inputValid
  unfold orElse
  cases result : first input with
  | ok value next =>
      rw [result] at firstResult
      exact firstResult
  | reject failure rejected => exact secondValid input inputValid
  | invariant error => trivial

/-- Transport a parser's successful value predicate pointwise. -/
theorem ValidFor.mono {α : Type} {parser : Parser α}
    {first second : SourceFile → α → Prop}
    (valid : parser.ValidFor first)
    (implies : ∀ file value, first file value → second file value) :
    parser.ValidFor second := by
  intro input inputValid
  exact (valid input inputValid).mono implies

end Parser

namespace State

/-- A parser-returned state remains valid and owned by the input file. -/
def ValueValidFor (file : SourceFile) (state : State) : Prop :=
  state.ValidFor ∧ state.file = file

end State

/-- Reading the current state preserves it as both value and continuation. -/
theorem getState_validFor :
    getState.ValidFor State.ValueValidFor := by
  intro input inputValid
  exact ⟨⟨inputValid, rfl⟩, inputValid, rfl⟩

/-- Reading the current state preserves its complete token window. -/
theorem getState_preservesTokenWindow :
    Parser.PreservesTokenWindow getState := by
  intro input
  exact ⟨rfl, rfl⟩

/-- Reading the current state leaves the token carrier unchanged. -/
theorem getState_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess getState := by
  intro input value next parsed
  unfold getState at parsed
  cases parsed
  rfl

/-- Reading the current state leaves the cursor in place. -/
theorem getState_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess getState := by
  intro input value next parsed
  unfold getState at parsed
  cases parsed
  exact Nat.le_refl _

/-- A validity- and file-preserving update defines a valid state parser. -/
theorem modifyState_validFor (update : State → State)
    (preserves : ∀ input, input.ValidFor →
      (update input).ValidFor ∧ (update input).file = input.file) :
    (modifyState update).ValidFor (fun _ _ => True) := by
  intro input inputValid
  unfold modifyState Reply.ValidFor
  exact ⟨trivial, (preserves input inputValid).1,
    (preserves input inputValid).2⟩

/-- A state update preserves the token window when its update function does. -/
theorem modifyState_preservesTokenWindow (update : State → State)
    (preserves : ∀ input,
      (update input).tokens = input.tokens ∧
        (update input).window = input.window) :
    Parser.PreservesTokenWindow (modifyState update) := by
  intro input
  unfold modifyState Reply.PreservesTokenWindow
  exact preserves input

/-- A state update preserves the carrier when its update function does. -/
theorem modifyState_preservesTokensOnSuccess (update : State → State)
    (preserves : ∀ input, (update input).tokens = input.tokens) :
    Parser.PreservesTokensOnSuccess (modifyState update) := by
  intro input value next parsed
  unfold modifyState at parsed
  cases parsed
  exact preserves input

/-- A state update is monotone when its update function is monotone. -/
theorem modifyState_cursorMonotoneOnSuccess (update : State → State)
    (monotone : ∀ input, input.cursor ≤ (update input).cursor) :
    Parser.CursorMonotoneOnSuccess (modifyState update) := by
  intro input value next parsed
  unfold modifyState at parsed
  cases parsed
  exact monotone input

/-- Emit one diagnostic known valid for this concrete input state. -/
theorem emitDiagnostic_reply_validFor {input : State}
    (inputValid : input.ValidFor) (diagnostic : ParseDiagnostic)
    (diagnosticValid : diagnostic.span.ValidFor input.file) :
    (emitDiagnostic diagnostic input).ValidFor input (fun _ _ => True) := by
  unfold emitDiagnostic modifyState Reply.ValidFor
  exact ⟨trivial, inputValid.emit_validFor diagnostic diagnosticValid, rfl⟩

/-- Emit a fixed diagnostic valid for every admitted input file. -/
theorem emitDiagnostic_validFor (diagnostic : ParseDiagnostic)
    (diagnosticValid : ∀ input : State, input.ValidFor →
      diagnostic.span.ValidFor input.file) :
    (emitDiagnostic diagnostic).ValidFor (fun _ _ => True) := by
  intro input inputValid
  exact emitDiagnostic_reply_validFor inputValid diagnostic
    (diagnosticValid input inputValid)

/-- Adding a diagnostic preserves the complete token window. -/
theorem emitDiagnostic_preservesTokenWindow
    (diagnostic : ParseDiagnostic) :
    Parser.PreservesTokenWindow (emitDiagnostic diagnostic) := by
  apply modifyState_preservesTokenWindow
  intro input
  exact ⟨rfl, rfl⟩

/-- Adding a diagnostic does not alter the immutable token carrier. -/
theorem emitDiagnostic_preservesTokensOnSuccess
    (diagnostic : ParseDiagnostic) :
    Parser.PreservesTokensOnSuccess (emitDiagnostic diagnostic) := by
  apply modifyState_preservesTokensOnSuccess
  intro input
  rfl

/-- Adding a diagnostic leaves the cursor in place. -/
theorem emitDiagnostic_cursorMonotoneOnSuccess
    (diagnostic : ParseDiagnostic) :
    Parser.CursorMonotoneOnSuccess (emitDiagnostic diagnostic) := by
  apply modifyState_cursorMonotoneOnSuccess
  intro input
  exact Nat.le_refl _

/-- Committing a valid failure diagnostic preserves state validity and file. -/
theorem emitFailure_validFor {state : State} (stateValid : state.ValidFor)
    (failure : Failure) (failureValid : failure.span.ValidFor state.file) :
    (emitFailure failure state).ValidFor ∧
      (emitFailure failure state).file = state.file := by
  refine ⟨?_, rfl⟩
  apply stateValid.emit_validFor
  exact failure.toDiagnostic_span_validFor failureValid

/-- Generic token acceptance satisfies the located-span contract. -/
theorem acceptToken_validFor (expected : ParseExpectation)
    (context : ParseContext) (accepts : TokenKind → Bool) :
    (acceptToken expected context accepts).ValidFor Located.ValidFor := by
  apply Parser.validFor_of_ok_reject
  · intro input inputValid value next result
    exact acceptToken_ok_validFor inputValid expected context accepts result
  · intro input inputValid failure next result
    exact acceptToken_reject_validFor inputValid expected context accepts result

theorem keyword_validFor (value : HardKeyword) (context : ParseContext) :
    (keyword value context).ValidFor Located.ValidFor := by
  exact acceptToken_validFor (.keyword value) context
    (· == .keyword value)

theorem symbol_validFor (value : Symbol) (context : ParseContext) :
    (symbol value context).ValidFor Located.ValidFor := by
  exact acceptToken_validFor (.symbol value) context
    (· == .symbol value)

theorem contextual_validFor (value : ContextualKeyword)
    (context : ParseContext) :
    (contextual value context).ValidFor Located.ValidFor := by
  exact acceptToken_validFor (.contextual value) context
    (·.isContextual value)

theorem rawIdentifier_validFor (context : ParseContext) :
    (rawIdentifier context).ValidFor Located.ValidFor := by
  apply Parser.validFor_of_ok_reject
  · intro input inputValid value next result
    exact rawIdentifier_ok_validFor inputValid context result
  · intro input inputValid failure next result
    exact rawIdentifier_reject_validFor inputValid context result

theorem identifier_validFor (context : ParseContext) :
    (identifier context).ValidFor Located.ValidFor := by
  apply Parser.validFor_of_ok_reject
  · intro input inputValid value next result
    exact identifier_ok_validFor inputValid context result
  · intro input inputValid failure next result
    exact identifier_reject_validFor inputValid context result

theorem yulIdentifier_validFor (context : ParseContext) :
    (yulIdentifier context).ValidFor Located.ValidFor := by
  apply Parser.validFor_of_ok_reject
  · intro input inputValid value next result
    exact yulIdentifier_ok_validFor inputValid context result
  · intro input inputValid failure next result
    exact yulIdentifier_reject_validFor inputValid context result

theorem coreLiteral_validFor :
    coreLiteral.ValidFor Located.ValidFor := by
  apply Parser.validFor_of_ok_reject
  · intro input inputValid value next result
    exact coreLiteral_ok_validFor inputValid result
  · intro input inputValid failure next result
    exact coreLiteral_reject_validFor inputValid result

theorem booleanIdentifier_validFor :
    booleanIdentifier.ValidFor Located.ValidFor := by
  apply Parser.validFor_of_ok_reject
  · intro input inputValid value next result
    exact booleanIdentifier_ok_validFor inputValid result
  · intro input inputValid failure next result
    exact booleanIdentifier_reject_validFor inputValid result

end Parser

end Solcore.Syntax
end

section
-- leanmerge: from Solcore.Syntax.Parser.PrimitiveCarrierProperties
/-! Immutable token-carrier laws for primitive canonical parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- An uncommitted rejection retains the input token array and window. -/
theorem rejectAt_preservesTokenWindow {α : Type} (state : State)
    (expected : NonemptyList ParseExpectation) (context : ParseContext) :
    (rejectAt (α := α) state expected context).PreservesTokenWindow state := by
  exact ⟨rfl, rfl⟩

/-- Generic token rejection returns the unchanged input state. -/
theorem acceptToken_reject_state_shape
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) {input next : State} {failure : Failure}
    (result : acceptToken expected context accepts input =
      .reject failure next) : next = input := by
  unfold acceptToken at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      cases result
      rfl
  | some token =>
      simp only [found] at result
      split at result
      · contradiction
      · unfold rejectAt at result
        cases result
        rfl

/-- Generic token acceptance preserves the token window on every reply. -/
theorem acceptToken_preservesTokenWindow
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) :
    Parser.PreservesTokenWindow (acceptToken expected context accepts) := by
  intro input
  cases result : acceptToken expected context accepts input with
  | ok token next =>
      rw [(acceptToken_ok_state_shape expected context accepts result).2]
      exact ⟨rfl, rfl⟩
  | reject failure next =>
      rw [acceptToken_reject_state_shape expected context accepts result]
      exact ⟨rfl, rfl⟩
  | invariant error => trivial

/-- Generic token acceptance changes only the parser cursor. -/
theorem acceptToken_preservesTokensOnSuccess
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) :
    Parser.PreservesTokensOnSuccess
      (acceptToken expected context accepts) := by
  intro input token next result
  rcases acceptToken_ok_state_shape expected context accepts result with
    ⟨_found, rfl⟩
  rfl

/-- Generic token acceptance advances by exactly one token on success. -/
theorem acceptToken_cursor_lt_onSuccess
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) {input next : State} {token : Token}
    (result : acceptToken expected context accepts input = .ok token next) :
    input.cursor < next.cursor := by
  rw [(acceptToken_ok_state_shape expected context accepts result).2]
  simp

theorem acceptToken_cursorMonotoneOnSuccess
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) :
    Parser.CursorMonotoneOnSuccess
      (acceptToken expected context accepts) := by
  intro input token next result
  exact Nat.le_of_lt
    (acceptToken_cursor_lt_onSuccess expected context accepts result)

/-- Generic token acceptance returns a span beginning at the input token. -/
theorem acceptToken_startsAtCurrentTokenOnSuccess
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) :
    Parser.StartsAtCurrentTokenOnSuccess
      (acceptToken expected context accepts) (·.span) := by
  intro input token next result
  exact ⟨token,
    (acceptToken_ok_state_shape expected context accepts result).1, rfl⟩

theorem keyword_preservesTokensOnSuccess
    (value : HardKeyword) (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (keyword value context) :=
  acceptToken_preservesTokensOnSuccess (.keyword value) context
    (· == .keyword value)

theorem keyword_preservesTokenWindow
    (value : HardKeyword) (context : ParseContext) :
    Parser.PreservesTokenWindow (keyword value context) :=
  acceptToken_preservesTokenWindow (.keyword value) context
    (· == .keyword value)

theorem keyword_cursorMonotoneOnSuccess
    (value : HardKeyword) (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (keyword value context) :=
  acceptToken_cursorMonotoneOnSuccess (.keyword value) context
    (· == .keyword value)

theorem symbol_preservesTokensOnSuccess
    (value : Symbol) (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (symbol value context) :=
  acceptToken_preservesTokensOnSuccess (.symbol value) context
    (· == .symbol value)

theorem symbol_preservesTokenWindow
    (value : Symbol) (context : ParseContext) :
    Parser.PreservesTokenWindow (symbol value context) :=
  acceptToken_preservesTokenWindow (.symbol value) context
    (· == .symbol value)

theorem symbol_cursorMonotoneOnSuccess
    (value : Symbol) (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (symbol value context) :=
  acceptToken_cursorMonotoneOnSuccess (.symbol value) context
    (· == .symbol value)

theorem symbol_startsAtCurrentTokenOnSuccess
    (value : Symbol) (context : ParseContext) :
    Parser.StartsAtCurrentTokenOnSuccess (symbol value context) (·.span) :=
  acceptToken_startsAtCurrentTokenOnSuccess (.symbol value) context
    (· == .symbol value)

theorem contextual_preservesTokensOnSuccess
    (value : ContextualKeyword) (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (contextual value context) :=
  acceptToken_preservesTokensOnSuccess (.contextual value) context
    (·.isContextual value)

theorem contextual_preservesTokenWindow
    (value : ContextualKeyword) (context : ParseContext) :
    Parser.PreservesTokenWindow (contextual value context) :=
  acceptToken_preservesTokenWindow (.contextual value) context
    (·.isContextual value)

theorem contextual_cursorMonotoneOnSuccess
    (value : ContextualKeyword) (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (contextual value context) :=
  acceptToken_cursorMonotoneOnSuccess (.contextual value) context
    (·.isContextual value)

theorem contextual_startsAtCurrentTokenOnSuccess
    (value : ContextualKeyword) (context : ParseContext) :
    Parser.StartsAtCurrentTokenOnSuccess (contextual value context) (·.span) :=
  acceptToken_startsAtCurrentTokenOnSuccess (.contextual value) context
    (·.isContextual value)

/-- Raw identifier success changes only the parser cursor. -/
theorem rawIdentifier_ok_state_shape (context : ParseContext)
    {input next : State} {name : Identifier}
    (result : rawIdentifier context input = .ok name next) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold rawIdentifier at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case identifier text => cases result; rfl

theorem rawIdentifier_preservesTokensOnSuccess (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (rawIdentifier context) := by
  intro input name next result
  rw [rawIdentifier_ok_state_shape context result]

/-- Raw identifiers preserve the token window on success and rejection. -/
theorem rawIdentifier_preservesTokenWindow (context : ParseContext) :
    Parser.PreservesTokenWindow (rawIdentifier context) := by
  intro input
  unfold rawIdentifier
  cases found : input.peek? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only
      all_goals try { exact rejectAt_preservesTokenWindow input _ _ }
      exact ⟨rfl, rfl⟩

theorem rawIdentifier_cursorMonotoneOnSuccess (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (rawIdentifier context) := by
  intro input name next result
  rw [rawIdentifier_ok_state_shape context result]
  simp

theorem identifier_preservesTokensOnSuccess (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (identifier context) := by
  intro input name next result
  exact (identifier_ok_state_shape context result).choose_spec.2.2.1

/-- Checked identifiers preserve the token window on success and rejection. -/
theorem identifier_preservesTokenWindow (context : ParseContext) :
    Parser.PreservesTokenWindow (identifier context) := by
  intro input
  unfold identifier
  cases raw : rawIdentifier context input with
  | ok name next =>
      have rawShape := rawIdentifier_preservesTokenWindow context input
      rw [raw] at rawShape
      change (if name.value.toList.contains '-' then
          Reply.ok name (next.emit {
            span := name.span
            kind := .invalidIdentifierHyphen name.value
          })
        else Reply.ok name next).PreservesTokenWindow input
      split
      · exact ⟨by simpa [State.emit] using rawShape.1,
          by simpa [State.emit] using rawShape.2⟩
      · exact rawShape
  | reject failure next =>
      have rawShape := rawIdentifier_preservesTokenWindow context input
      rw [raw] at rawShape
      change (Reply.reject failure next).PreservesTokenWindow input
      exact rawShape
  | invariant error =>
      change (Reply.invariant error).PreservesTokenWindow input
      trivial

theorem identifier_cursorMonotoneOnSuccess (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (identifier context) := by
  intro input name next result
  rw [(identifier_ok_state_shape context result).choose_spec.2.2.2]
  simp

/-- Yul identifier success changes only the parser cursor. -/
theorem yulIdentifier_ok_state_shape (context : ParseContext)
    {input next : State} {name : Identifier}
    (result : yulIdentifier context input = .ok name next) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold yulIdentifier at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case yulIdentifier text => cases result; rfl

theorem yulIdentifier_preservesTokensOnSuccess (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (yulIdentifier context) := by
  intro input name next result
  rw [yulIdentifier_ok_state_shape context result]

/-- Primitive Yul identifiers preserve every ordinary token window. -/
theorem yulIdentifier_preservesTokenWindow (context : ParseContext) :
    Parser.PreservesTokenWindow (yulIdentifier context) := by
  intro input
  unfold yulIdentifier
  cases found : input.peek? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only
      all_goals try { exact rejectAt_preservesTokenWindow input _ _ }
      exact ⟨rfl, rfl⟩

theorem yulIdentifier_cursorMonotoneOnSuccess (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (yulIdentifier context) := by
  intro input name next result
  rw [yulIdentifier_ok_state_shape context result]
  simp

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Name
set_option autoImplicit false

namespace Solcore.Syntax.Parser

open QualifiedNameInternals

private theorem qualifiedNameTail_validFor
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev state firstIndex firstToken,
      state.ValidFor →
      first.span.ValidFor state.file →
      last.span.ValidFor state.file →
      (∀ component ∈ tailRev, component.span.ValidFor state.file) →
      first.span.startByte ≤ last.span.endByte →
      state.tokens[firstIndex]? = some firstToken →
      firstToken.span = first.span →
      firstIndex < state.cursor →
      (qualifiedNameTail context phase first fuel last tailRev state).ValidFor
        state QualifiedName.ValidFor := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev state firstIndex firstToken stateValid firstValid
        lastValid tailValid firstBeforeLast firstFound firstSpan
        firstBeforeCursor
      trivial
  | succ fuel inductionHypothesis =>
      intro last tailRev state firstIndex firstToken stateValid firstValid
        lastValid tailValid firstBeforeLast firstFound firstSpan
        firstBeforeCursor
      unfold qualifiedNameTail
      split
      · cases dotResult : symbol .dot context state with
        | invariant error =>
            simp only [Reply.ValidFor]
        | reject failure rejected =>
            have dotValid := symbol_validFor .dot context state stateValid
            rw [dotResult] at dotValid
            simpa only [Reply.ValidFor] using dotValid
        | ok dot afterDot =>
            have dotValid := symbol_validFor .dot context state stateValid
            rw [dotResult] at dotValid
            have dotShape := symbol_ok_state_shape .dot context dotResult
            simp only
            cases componentResult : identifier context afterDot with
            | invariant error =>
                simp only [Reply.ValidFor]
            | reject failure rejected =>
                have componentValid :=
                  identifier_validFor context afterDot dotValid.2.1
                rw [componentResult] at componentValid
                simpa only [Reply.ValidFor] using
                  componentValid.of_file_eq dotValid.2.2
            | ok component next =>
                have componentValid :=
                  identifier_validFor context afterDot dotValid.2.1
                rw [componentResult] at componentValid
                rcases identifier_ok_state_shape context componentResult with
                  ⟨componentToken, componentFound, componentSpan,
                    componentTokens, componentCursor⟩
                have componentFoundInState :
                    state.tokens[state.cursor + 1]? = some componentToken := by
                  have foundAtCursor :=
                    State.getElem?_eq_some_of_peek?_eq_some componentFound
                  simpa [dotShape.2] using foundAtCursor
                have firstBeforeComponentIndex :
                    firstIndex < state.cursor + 1 :=
                  Nat.lt_of_lt_of_le firstBeforeCursor
                    (Nat.le_add_right state.cursor 1)
                have firstEndBeforeComponentStart :
                    first.span.endByte ≤ component.span.startByte := by
                  have ordered :=
                    stateValid.token_end_le_token_start_of_getElem?_lt
                      firstFound componentFoundInState
                      firstBeforeComponentIndex
                  simpa [firstSpan, componentSpan] using ordered
                have firstBeforeComponent :
                    first.span.startByte ≤ component.span.endByte :=
                  Nat.le_trans firstValid.2.1
                    (Nat.le_trans firstEndBeforeComponentStart
                      (by
                        have spanValid :
                            component.span.ValidFor afterDot.file := by
                          simpa only [Located.ValidFor] using componentValid.1
                        exact spanValid.2.1))
                have firstValidNext : first.span.ValidFor next.file := by
                  simpa [componentValid.2.2, dotValid.2.2] using firstValid
                have componentValidNext :
                    component.span.ValidFor next.file := by
                  have spanValid : component.span.ValidFor afterDot.file := by
                    simpa only [Located.ValidFor] using componentValid.1
                  simpa [componentValid.2.2] using spanValid
                have tailValidNext : ∀ item ∈ component :: tailRev,
                    item.span.ValidFor next.file := by
                  intro item member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact componentValidNext
                  · simpa [componentValid.2.2, dotValid.2.2] using
                      tailValid item member
                have firstFoundNext :
                    next.tokens[firstIndex]? = some firstToken := by
                  simpa [componentTokens, dotShape.2] using firstFound
                have firstBeforeNextCursor : firstIndex < next.cursor := by
                  have firstBeforeAfterDot : firstIndex < afterDot.cursor := by
                    rw [dotShape.2]
                    exact Nat.lt_of_lt_of_le firstBeforeCursor
                      (Nat.le_add_right state.cursor 1)
                  rw [componentCursor]
                  exact Nat.lt_of_lt_of_le firstBeforeAfterDot
                    (Nat.le_add_right afterDot.cursor 1)
                have recursiveValid :=
                  inductionHypothesis component (component :: tailRev) next
                    firstIndex firstToken componentValid.2.1 firstValidNext
                    componentValidNext tailValidNext firstBeforeComponent
                    firstFoundNext firstSpan firstBeforeNextCursor
                simpa only using recursiveValid.of_file_eq
                  (componentValid.2.2.trans dotValid.2.2)
      · unfold finishQualifiedName Reply.ValidFor QualifiedName.ValidFor
        refine ⟨⟨?_, ?_⟩, stateValid, rfl⟩
        · exact SourceSpan.cover_validFor firstValid lastValid firstBeforeLast
        · intro component member
          simp only [NonemptyList.toList, List.mem_cons,
            List.mem_reverse] at member
          rcases member with rfl | member
          · exact firstValid
          · exact tailValid component member

/-- Qualified-name parsing preserves every component and covering source span. -/
theorem qualifiedName_validFor (context : ParseContext) (phase : ParserPhase) :
    (qualifiedName context phase).ValidFor QualifiedName.ValidFor := by
  intro input inputValid
  unfold qualifiedName
  cases firstResult : identifier context input with
  | invariant error =>
      simp only [Reply.ValidFor]
  | reject failure rejected =>
      have firstValid := identifier_validFor context input inputValid
      rw [firstResult] at firstValid
      simpa only [Reply.ValidFor] using firstValid
  | ok first next =>
      have firstValid := identifier_validFor context input inputValid
      rw [firstResult] at firstValid
      rcases identifier_ok_state_shape context firstResult with
        ⟨firstToken, firstFound, firstSpan, firstTokens, firstCursor⟩
      have firstFoundNext :
          next.tokens[input.cursor]? = some firstToken := by
        have foundAtCursor :=
          State.getElem?_eq_some_of_peek?_eq_some firstFound
        simpa [firstTokens] using foundAtCursor
      have firstValidNext : first.span.ValidFor next.file := by
        have spanValid : first.span.ValidFor input.file := by
          simpa only [Located.ValidFor] using firstValid.1
        simpa [firstValid.2.2] using spanValid
      have tailValid := qualifiedNameTail_validFor context phase first
        (next.remainingCount + 1) first [] next input.cursor firstToken
        firstValid.2.1 firstValidNext firstValidNext
        (by simp) firstValidNext.2.1 firstFoundNext firstSpan
        (by rw [firstCursor]; simp)
      simpa only using tailValid.of_file_eq firstValid.2.2

private theorem qualifiedNameTail_ok_state_shape
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev input name next,
      qualifiedNameTail context phase first fuel last tailRev input =
        .ok name next →
      next.tokens = input.tokens ∧
        name.span.startByte = first.span.startByte := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input name next result
      contradiction
  | succ fuel inductionHypothesis =>
      intro last tailRev input name next result
      unfold qualifiedNameTail at result
      split at result
      · cases dotResult : symbol .dot context input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : identifier context afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                have recursiveShape := inductionHypothesis component
                  (component :: tailRev) afterComponent name next result
                have dotShape :=
                  symbol_ok_state_shape .dot context dotResult
                rcases identifier_ok_state_shape context componentResult with
                  ⟨_token, _found, _span, componentTokens, _cursor⟩
                have dotTokens : afterDot.tokens = input.tokens := by
                  rw [dotShape.2]
                exact ⟨recursiveShape.1.trans
                    (componentTokens.trans dotTokens), recursiveShape.2⟩
      · unfold finishQualifiedName at result
        cases result
        exact ⟨rfl, rfl⟩

/--
A successful qualified name starts at its first input token and leaves the
immutable token carrier unchanged.
-/
theorem qualifiedName_ok_state_shape (context : ParseContext)
    (phase : ParserPhase) {input next : State} {name : QualifiedName}
    (result : qualifiedName context phase input = .ok name next) :
    ∃ firstToken,
      input.peek? = some firstToken ∧
        firstToken.span.startByte = name.span.startByte ∧
        next.tokens = input.tokens := by
  unfold qualifiedName at result
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      have tailShape := qualifiedNameTail_ok_state_shape context phase first
        (afterFirst.remainingCount + 1) first [] afterFirst name next result
      rcases identifier_ok_state_shape context firstResult with
        ⟨firstToken, found, span, tokens, _cursor⟩
      refine ⟨firstToken, found, ?_, tailShape.1.trans tokens⟩
      rw [span]
      exact tailShape.2.symm

/-- Qualified-name success preserves the immutable token carrier. -/
theorem qualifiedName_preservesTokensOnSuccess (context : ParseContext)
    (phase : ParserPhase) :
    Parser.PreservesTokensOnSuccess (qualifiedName context phase) := by
  intro input name next result
  exact (qualifiedName_ok_state_shape context phase result).choose_spec.2.2

private theorem qualifiedNameTail_preservesTokenWindow
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev,
      Parser.PreservesTokenWindow
        (qualifiedNameTail context phase first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input
      trivial
  | succ fuel inductionHypothesis =>
      intro last tailRev input
      unfold qualifiedNameTail
      split
      · have dotShape := symbol_preservesTokenWindow .dot context input
        cases dotResult : symbol .dot context input with
        | invariant error => trivial
        | reject failure rejected =>
            rw [dotResult] at dotShape
            exact dotShape
        | ok dot afterDot =>
            rw [dotResult] at dotShape
            have componentShape := identifier_preservesTokenWindow context afterDot
            cases componentResult : identifier context afterDot with
            | invariant error =>
                simp only [componentResult, Reply.PreservesTokenWindow]
            | reject failure rejected =>
                rw [componentResult] at componentShape
                simp only [componentResult]
                exact componentShape.trans dotShape
            | ok component afterComponent =>
                rw [componentResult] at componentShape
                simp only [componentResult]
                exact (inductionHypothesis component (component :: tailRev)
                  afterComponent).trans (componentShape.trans dotShape)
      · exact ⟨rfl, rfl⟩

/-- Qualified names preserve tokens and the active window on every reply. -/
theorem qualifiedName_preservesTokenWindow (context : ParseContext)
    (phase : ParserPhase) :
    Parser.PreservesTokenWindow (qualifiedName context phase) := by
  intro input
  unfold qualifiedName
  have firstShape := identifier_preservesTokenWindow context input
  cases firstResult : identifier context input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [firstResult] at firstShape
      exact firstShape
  | ok first afterFirst =>
      rw [firstResult] at firstShape
      exact (qualifiedNameTail_preservesTokenWindow context phase first
        (afterFirst.remainingCount + 1) first [] afterFirst).trans firstShape

/-- A qualified name starts at the first identifier token it retains. -/
theorem qualifiedName_startsAtCurrentTokenOnSuccess
    (context : ParseContext) (phase : ParserPhase) :
    Parser.StartsAtCurrentTokenOnSuccess
      (qualifiedName context phase) (·.span) := by
  intro input name next result
  rcases qualifiedName_ok_state_shape context phase result with
    ⟨firstToken, found, start, _tokens⟩
  exact ⟨firstToken, found, start⟩

private theorem qualifiedNameTail_cursorMonotoneOnSuccess
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev input name next,
      qualifiedNameTail context phase first fuel last tailRev input =
        .ok name next →
      input.cursor ≤ next.cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input name next result
      contradiction
  | succ fuel inductionHypothesis =>
      intro last tailRev input name next result
      unfold qualifiedNameTail at result
      split at result
      · cases dotResult : symbol .dot context input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : identifier context afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                have dotMonotone := symbol_cursorMonotoneOnSuccess
                  .dot context input dot afterDot dotResult
                have componentMonotone :=
                  identifier_cursorMonotoneOnSuccess context afterDot
                    component afterComponent componentResult
                have recursiveMonotone := inductionHypothesis component
                  (component :: tailRev) afterComponent name next result
                exact Nat.le_trans dotMonotone
                  (Nat.le_trans componentMonotone recursiveMonotone)
      · unfold finishQualifiedName at result
        cases result
        exact Nat.le_refl _

/-- Every successful qualified name consumes its first identifier. -/
theorem qualifiedName_cursor_lt_onSuccess (context : ParseContext)
    (phase : ParserPhase) {input next : State} {name : QualifiedName}
    (result : qualifiedName context phase input = .ok name next) :
    input.cursor < next.cursor := by
  unfold qualifiedName at result
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      have firstProgress : input.cursor < afterFirst.cursor := by
        rw [(identifier_ok_state_shape context firstResult).choose_spec.2.2.2]
        simp
      have tailMonotone := qualifiedNameTail_cursorMonotoneOnSuccess
        context phase first (afterFirst.remainingCount + 1) first []
          afterFirst name next result
      exact Nat.lt_of_lt_of_le firstProgress tailMonotone

/-- Successful qualified-name parsing never rewinds the cursor. -/
theorem qualifiedName_cursorMonotoneOnSuccess (context : ParseContext)
    (phase : ParserPhase) :
    Parser.CursorMonotoneOnSuccess (qualifiedName context phase) := by
  intro input name next result
  exact Nat.le_of_lt (qualifiedName_cursor_lt_onSuccess context phase result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Delimited
set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem closeDelimited_validFor {α : Type}
    (elementValid : SourceFile → α → Prop)
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) (state : State) (openingIndex : Nat)
    (stateValid : state.ValidFor)
    (openingValid : opening.span.ValidFor state.file)
    (elementsValid : ∀ element ∈ elementsRev,
      elementValid state.file element)
    (openingFound : state.tokens[openingIndex]? = some opening)
    (openingBeforeCursor : openingIndex < state.cursor) :
    (closeDelimited opening closing context elementsRev state).ValidFor
      state (DelimitedList.ValidFor elementValid) := by
  unfold closeDelimited
  cases closingResult : symbol closing context state with
  | invariant error => simp only [Reply.ValidFor]
  | reject failure rejected =>
      have closingValid := symbol_validFor closing context state stateValid
      rw [closingResult] at closingValid
      simpa only [Reply.ValidFor] using closingValid
  | ok closingToken next =>
      have closingValid := symbol_validFor closing context state stateValid
      rw [closingResult] at closingValid
      have closingShape := symbol_ok_state_shape closing context closingResult
      have closingFound :=
        State.getElem?_eq_some_of_peek?_eq_some closingShape.1
      have openingBeforeClosing :=
        stateValid.token_end_le_token_start_of_getElem?_lt
          openingFound closingFound openingBeforeCursor
      have closingSpanValid : closingToken.span.ValidFor state.file := by
        simpa only [Located.ValidFor] using closingValid.1
      have coverValid :
          (SourceSpan.cover opening.span closingToken.span).ValidFor state.file := by
        apply SourceSpan.cover_validFor openingValid closingSpanValid
        exact Nat.le_trans openingValid.2.1
          (Nat.le_trans openingBeforeClosing closingSpanValid.2.1)
      simp only
      unfold Reply.ValidFor DelimitedList.ValidFor
      refine ⟨⟨coverValid, ?_⟩, closingValid.2.1, closingValid.2.2⟩
      intro element member
      exact elementsValid element (by simpa using member)

private theorem afterDelimitedElement_validFor {α : Type}
    (elementValid : SourceFile → α → Prop) (element : Parser α)
    (elementContract : element.ValidFor elementValid)
    (elementShape : Parser.PreservesTokensOnSuccess element)
    (closing : Symbol) (allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev state openingIndex,
      state.ValidFor →
      opening.span.ValidFor state.file →
      (∀ value ∈ elementsRev, elementValid state.file value) →
      state.tokens[openingIndex]? = some opening →
      openingIndex < state.cursor →
      (afterDelimitedElement element closing allowTrailing context phase opening
        fuel elementsRev state).ValidFor state
          (DelimitedList.ValidFor elementValid) := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev state openingIndex stateValid openingValid
        elementsValid openingFound openingBeforeCursor
      trivial
  | succ fuel inductionHypothesis =>
      intro elementsRev state openingIndex stateValid openingValid
        elementsValid openingFound openingBeforeCursor
      unfold afterDelimitedElement
      split
      · cases commaResult : symbol .comma context state with
        | invariant error => simp only [Reply.ValidFor]
        | reject failure rejected =>
            have commaValid := symbol_validFor .comma context state stateValid
            rw [commaResult] at commaValid
            simpa only [Reply.ValidFor] using commaValid
        | ok comma afterComma =>
            have commaValid := symbol_validFor .comma context state stateValid
            rw [commaResult] at commaValid
            have commaShape := symbol_ok_state_shape .comma context commaResult
            have openingValidAfterComma :
                opening.span.ValidFor afterComma.file := by
              simpa [commaValid.2.2] using openingValid
            have elementsValidAfterComma : ∀ value ∈ elementsRev,
                elementValid afterComma.file value := by
              intro value member
              simpa [commaValid.2.2] using elementsValid value member
            have openingFoundAfterComma :
                afterComma.tokens[openingIndex]? = some opening := by
              simpa [commaShape.2] using openingFound
            have openingBeforeAfterComma : openingIndex < afterComma.cursor := by
              rw [commaShape.2]
              exact Nat.lt_of_lt_of_le openingBeforeCursor
                (Nat.le_add_right state.cursor 1)
            simp only
            split
            · have closed := closeDelimited_validFor elementValid opening
                closing context elementsRev afterComma openingIndex
                commaValid.2.1 openingValidAfterComma
                elementsValidAfterComma openingFoundAfterComma
                openingBeforeAfterComma
              exact closed.of_file_eq commaValid.2.2
            · cases elementResult : element afterComma with
              | invariant error => simp only [Reply.ValidFor]
              | reject failure rejected =>
                  have valueValid := elementContract afterComma commaValid.2.1
                  rw [elementResult] at valueValid
                  simpa only [Reply.ValidFor] using
                    valueValid.of_file_eq commaValid.2.2
              | ok value next =>
                  have valueValid := elementContract afterComma commaValid.2.1
                  rw [elementResult] at valueValid
                  have tokensEq := elementShape afterComma value next elementResult
                  simp only
                  split
                  · have openingValidNext :
                        opening.span.ValidFor next.file := by
                      simpa [valueValid.2.2] using openingValidAfterComma
                    have valueValidNext : elementValid next.file value := by
                      simpa [valueValid.2.2] using valueValid.1
                    have elementsValidNext : ∀ item ∈ value :: elementsRev,
                        elementValid next.file item := by
                      intro item member
                      rcases List.mem_cons.mp member with rfl | member
                      · exact valueValidNext
                      · simpa [valueValid.2.2] using
                          elementsValidAfterComma item member
                    have openingFoundNext :
                        next.tokens[openingIndex]? = some opening := by
                      simpa [tokensEq] using openingFoundAfterComma
                    have recursiveValid := inductionHypothesis
                      (value :: elementsRev) next openingIndex valueValid.2.1
                      openingValidNext elementsValidNext openingFoundNext
                      (Nat.lt_trans openingBeforeAfterComma (by assumption))
                    exact recursiveValid.of_file_eq
                      (valueValid.2.2.trans commaValid.2.2)
                  · simp only [Reply.ValidFor]
      · split
        · exact closeDelimited_validFor elementValid opening closing context
            elementsRev state openingIndex stateValid openingValid
            elementsValid openingFound openingBeforeCursor
        · unfold rejectAt Reply.ValidFor
          exact ⟨stateValid.currentSpan_validFor, stateValid, rfl⟩

/-- A valid, token-preserving element parser lifts through delimiter policy. -/
theorem delimitedWithPolicy_validFor {α : Type}
    (elementValid : SourceFile → α → Prop)
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (elementContract : element.ValidFor elementValid)
    (elementShape : Parser.PreservesTokensOnSuccess element) :
    (delimitedWithPolicy opening closing allowEmpty allowTrailing element
      context phase).ValidFor (DelimitedList.ValidFor elementValid) := by
  intro input inputValid
  unfold delimitedWithPolicy
  cases openingResult : symbol opening context input with
  | invariant error => simp only [Reply.ValidFor]
  | reject failure rejected =>
      have openingValid := symbol_validFor opening context input inputValid
      rw [openingResult] at openingValid
      simpa only [Reply.ValidFor] using openingValid
  | ok openingToken afterOpening =>
      have openingValid := symbol_validFor opening context input inputValid
      rw [openingResult] at openingValid
      have openingShape := symbol_ok_state_shape opening context openingResult
      have openingSpanValid : openingToken.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using openingValid.1
      have openingFoundInput :=
        State.getElem?_eq_some_of_peek?_eq_some openingShape.1
      have openingSpanValidAfter :
          openingToken.span.ValidFor afterOpening.file := by
        simpa [openingValid.2.2] using openingSpanValid
      have openingFoundAfter :
          afterOpening.tokens[input.cursor]? = some openingToken := by
        simpa [openingShape.2] using openingFoundInput
      have openingBeforeAfter : input.cursor < afterOpening.cursor := by
        rw [openingShape.2]
        simp
      simp only
      split
      · have closed := closeDelimited_validFor elementValid openingToken
          closing context [] afterOpening input.cursor openingValid.2.1
          openingSpanValidAfter (by simp) openingFoundAfter openingBeforeAfter
        exact closed.of_file_eq openingValid.2.2
      · cases elementResult : element afterOpening with
        | invariant error => simp only [Reply.ValidFor]
        | reject failure rejected =>
            have valueValid := elementContract afterOpening openingValid.2.1
            rw [elementResult] at valueValid
            simpa only [Reply.ValidFor] using
              valueValid.of_file_eq openingValid.2.2
        | ok value next =>
            have valueValid := elementContract afterOpening openingValid.2.1
            rw [elementResult] at valueValid
            have tokensEq := elementShape afterOpening value next elementResult
            simp only
            split
            · have openingSpanValidNext :
                  openingToken.span.ValidFor next.file := by
                simpa [valueValid.2.2] using openingSpanValidAfter
              have valueValidNext : elementValid next.file value := by
                simpa [valueValid.2.2] using valueValid.1
              have openingFoundNext :
                  next.tokens[input.cursor]? = some openingToken := by
                simpa [tokensEq] using openingFoundAfter
              have tailValid := afterDelimitedElement_validFor elementValid
                element elementContract elementShape closing allowTrailing
                context phase openingToken (afterOpening.remainingCount + 1)
                [value] next input.cursor valueValid.2.1
                openingSpanValidNext (by
                  intro item member
                  simp only [List.mem_singleton] at member
                  subst item
                  exact valueValidNext)
                openingFoundNext
                (Nat.lt_trans openingBeforeAfter (by assumption))
              exact tailValid.of_file_eq
                (valueValid.2.2.trans openingValid.2.2)
            · simp only [Reply.ValidFor]

/-- Trailing-comma lists preserve delimiter and element provenance. -/
theorem delimited_validFor {α : Type}
    (elementValid : SourceFile → α → Prop)
    (opening closing : Symbol) (allowEmpty : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (elementContract : element.ValidFor elementValid)
    (elementShape : Parser.PreservesTokensOnSuccess element) :
    (delimited opening closing allowEmpty element context phase).ValidFor
      (DelimitedList.ValidFor elementValid) := by
  exact delimitedWithPolicy_validFor elementValid opening closing allowEmpty
    true element context phase elementContract elementShape

/-- Non-trailing-comma lists preserve delimiter and element provenance. -/
theorem delimitedNoTrailing_validFor {α : Type}
    (elementValid : SourceFile → α → Prop)
    (opening closing : Symbol) (allowEmpty : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (elementContract : element.ValidFor elementValid)
    (elementShape : Parser.PreservesTokensOnSuccess element) :
    (delimitedNoTrailing opening closing allowEmpty element context phase).ValidFor
      (DelimitedList.ValidFor elementValid) := by
  exact delimitedWithPolicy_validFor elementValid opening closing allowEmpty
    false element context phase elementContract elementShape

private theorem closeDelimited_preservesTokenWindow {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) :
    Parser.PreservesTokenWindow
      (closeDelimited opening closing context elementsRev) := by
  intro input
  unfold closeDelimited
  have closingShape := symbol_preservesTokenWindow closing context input
  cases result : symbol closing context input with
  | ok token next => rw [result] at closingShape; exact closingShape
  | reject failure next => rw [result] at closingShape; exact closingShape
  | invariant error => trivial

private theorem afterDelimitedElement_preservesTokenWindow {α : Type}
    (element : Parser α) (elementShape : Parser.PreservesTokenWindow element)
    (closing : Symbol) (allowTrailing : Bool) (context : ParseContext)
    (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev,
      Parser.PreservesTokenWindow
        (afterDelimitedElement element closing allowTrailing context phase
          opening fuel elementsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input
      simp only [afterDelimitedElement, Reply.PreservesTokenWindow]
  | succ fuel inductionHypothesis =>
      intro elementsRev input
      unfold afterDelimitedElement
      split
      · have commaShape := symbol_preservesTokenWindow .comma context input
        cases commaResult : symbol .comma context input with
        | ok comma afterComma =>
            rw [commaResult] at commaShape
            simp only
            split
            · exact (closeDelimited_preservesTokenWindow opening closing context
                elementsRev afterComma).trans commaShape
            · have itemShape := elementShape afterComma
              cases itemResult : element afterComma with
              | ok value afterElement =>
                  rw [itemResult] at itemShape
                  simp only
                  split
                  · exact (inductionHypothesis (value :: elementsRev)
                      afterElement).trans (itemShape.trans commaShape)
                  · trivial
              | reject failure rejected =>
                  rw [itemResult] at itemShape
                  exact itemShape.trans commaShape
              | invariant error => trivial
        | reject failure rejected =>
            rw [commaResult] at commaShape
            exact commaShape
        | invariant error => trivial
      · split
        · exact closeDelimited_preservesTokenWindow opening closing context
            elementsRev input
        · exact rejectAt_preservesTokenWindow input _ _

/-- Delimiter parsing preserves every ordinary token window. -/
theorem delimitedWithPolicy_preservesTokenWindow {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (elementShape : Parser.PreservesTokenWindow element) :
    Parser.PreservesTokenWindow
      (delimitedWithPolicy opening closing allowEmpty allowTrailing element
        context phase) := by
  intro input
  unfold delimitedWithPolicy
  have openingShape := symbol_preservesTokenWindow opening context input
  cases openingResult : symbol opening context input with
  | ok openingToken afterOpening =>
      rw [openingResult] at openingShape
      simp only
      split
      · exact (closeDelimited_preservesTokenWindow openingToken closing context
          [] afterOpening).trans openingShape
      · have itemShape := elementShape afterOpening
        cases itemResult : element afterOpening with
        | ok value afterElement =>
            rw [itemResult] at itemShape
            simp only
            split
            · exact (afterDelimitedElement_preservesTokenWindow element
                elementShape closing allowTrailing context phase openingToken
                (afterOpening.remainingCount + 1) [value] afterElement).trans
                (itemShape.trans openingShape)
            · trivial
        | reject failure rejected =>
            rw [itemResult] at itemShape
            exact itemShape.trans openingShape
        | invariant error => trivial
  | reject failure rejected =>
      rw [openingResult] at openingShape
      exact openingShape
  | invariant error => trivial

theorem delimited_preservesTokenWindow {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    (elementShape : Parser.PreservesTokenWindow element) :
    Parser.PreservesTokenWindow
      (delimited opening closing allowEmpty element context phase) :=
  delimitedWithPolicy_preservesTokenWindow opening closing allowEmpty true
    element context phase elementShape

private theorem closeDelimited_preservesTokensOnSuccess {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) :
    Parser.PreservesTokensOnSuccess
      (closeDelimited opening closing context elementsRev) := by
  intro input values next result
  unfold closeDelimited at result
  cases closingResult : symbol closing context input with
  | ok token afterClosing =>
      simp only [closingResult] at result
      cases result
      exact (symbol_ok_state_shape closing context closingResult).2 ▸ rfl
  | reject failure rejected =>
      simp only [closingResult] at result
      contradiction
  | invariant error =>
      simp only [closingResult] at result
      contradiction

private theorem afterDelimitedElement_preservesTokensOnSuccess {α : Type}
    (element : Parser α) (elementShape : Parser.PreservesTokensOnSuccess element)
    (closing : Symbol) (allowTrailing : Bool) (context : ParseContext)
    (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev,
      Parser.PreservesTokensOnSuccess
        (afterDelimitedElement element closing allowTrailing context phase
          opening fuel elementsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input values next result
      simp only [afterDelimitedElement] at result
      contradiction
  | succ fuel inductionHypothesis =>
      intro elementsRev input values next result
      unfold afterDelimitedElement at result
      split at result
      · cases commaResult : symbol .comma context input with
        | ok comma afterComma =>
            simp only [commaResult] at result
            have commaTokens : afterComma.tokens = input.tokens :=
              (symbol_ok_state_shape .comma context commaResult).2 ▸ rfl
            split at result
            · exact (closeDelimited_preservesTokensOnSuccess opening closing
                context elementsRev afterComma values next result).trans
                commaTokens
            · cases elementResult : element afterComma with
              | ok value afterElement =>
                  simp only [elementResult] at result
                  split at result
                  · exact (inductionHypothesis (value :: elementsRev)
                      afterElement values next result).trans
                      ((elementShape afterComma value afterElement
                        elementResult).trans commaTokens)
                  · contradiction
              | reject failure rejected =>
                  simp only [elementResult] at result
                  contradiction
              | invariant error =>
                  simp only [elementResult] at result
                  contradiction
        | reject failure rejected =>
            simp only [commaResult] at result
            contradiction
        | invariant error =>
            simp only [commaResult] at result
            contradiction
      · split at result
        · exact closeDelimited_preservesTokensOnSuccess opening closing context
            elementsRev input values next result
        · unfold rejectAt at result
          contradiction

/-- Delimited parsing never replaces or reorders the immutable token carrier. -/
theorem delimitedWithPolicy_preservesTokensOnSuccess {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    (elementShape : Parser.PreservesTokensOnSuccess element) :
    Parser.PreservesTokensOnSuccess
      (delimitedWithPolicy opening closing allowEmpty allowTrailing element
        context phase) := by
  intro input values next result
  unfold delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | ok openingToken afterOpening =>
      simp only [openingResult] at result
      have openingTokens : afterOpening.tokens = input.tokens :=
        (symbol_ok_state_shape opening context openingResult).2 ▸ rfl
      split at result
      · exact (closeDelimited_preservesTokensOnSuccess openingToken closing
          context [] afterOpening values next result).trans openingTokens
      · cases elementResult : element afterOpening with
        | ok value afterElement =>
            simp only [elementResult] at result
            split at result
            · exact (afterDelimitedElement_preservesTokensOnSuccess element
                elementShape closing allowTrailing context phase openingToken
                (afterOpening.remainingCount + 1) [value] afterElement values
                next result).trans
                ((elementShape afterOpening value afterElement
                  elementResult).trans openingTokens)
            · contradiction
        | reject failure rejected =>
            simp only [elementResult] at result
            contradiction
        | invariant error =>
            simp only [elementResult] at result
            contradiction
  | reject failure rejected =>
      simp only [openingResult] at result
      contradiction
  | invariant error =>
      simp only [openingResult] at result
      contradiction

theorem delimited_preservesTokensOnSuccess {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    (elementShape : Parser.PreservesTokensOnSuccess element) :
    Parser.PreservesTokensOnSuccess
      (delimited opening closing allowEmpty element context phase) :=
  delimitedWithPolicy_preservesTokensOnSuccess opening closing allowEmpty true
    element context phase elementShape

theorem delimitedNoTrailing_preservesTokensOnSuccess {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    (elementShape : Parser.PreservesTokensOnSuccess element) :
    Parser.PreservesTokensOnSuccess
      (delimitedNoTrailing opening closing allowEmpty element context phase) :=
  delimitedWithPolicy_preservesTokensOnSuccess opening closing allowEmpty false
    element context phase elementShape

private theorem closeDelimited_startsAtOpening {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) {input next : State}
    {values : DelimitedList α}
    (result : closeDelimited opening closing context elementsRev input =
      .ok values next) :
    values.span.startByte = opening.span.startByte := by
  unfold closeDelimited at result
  cases closingResult : symbol closing context input with
  | ok token afterClosing =>
      simp only [closingResult] at result
      cases result
      rfl
  | reject failure rejected =>
      simp only [closingResult] at result
      contradiction
  | invariant error =>
      simp only [closingResult] at result
      contradiction

private theorem afterDelimitedElement_startsAtOpening {α : Type}
    (element : Parser α) (closing : Symbol) (allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev input values next,
      afterDelimitedElement element closing allowTrailing context phase opening
          fuel elementsRev input = .ok values next →
        values.span.startByte = opening.span.startByte := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input values next result
      simp only [afterDelimitedElement] at result
      contradiction
  | succ fuel inductionHypothesis =>
      intro elementsRev input values next result
      unfold afterDelimitedElement at result
      split at result
      · cases commaResult : symbol .comma context input with
        | ok comma afterComma =>
            simp only [commaResult] at result
            split at result
            · exact closeDelimited_startsAtOpening opening closing context
                elementsRev result
            · cases elementResult : element afterComma with
              | ok value afterElement =>
                  simp only [elementResult] at result
                  split at result
                  · exact inductionHypothesis (value :: elementsRev)
                      afterElement values next result
                  · contradiction
              | reject failure rejected =>
                  simp only [elementResult] at result
                  contradiction
              | invariant error =>
                  simp only [elementResult] at result
                  contradiction
        | reject failure rejected =>
            simp only [commaResult] at result
            contradiction
        | invariant error =>
            simp only [commaResult] at result
            contradiction
      · split at result
        · exact closeDelimited_startsAtOpening opening closing context
            elementsRev result
        · unfold rejectAt at result
          contradiction

/-- A delimited result starts at the opening token of the input state. -/
theorem delimitedWithPolicy_startsAtCurrentTokenOnSuccess {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase) :
    Parser.StartsAtCurrentTokenOnSuccess
      (delimitedWithPolicy opening closing allowEmpty allowTrailing element
        context phase) (·.span) := by
  intro input values next result
  unfold delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | ok openingToken afterOpening =>
      simp only [openingResult] at result
      have openingFound :=
        (symbol_ok_state_shape opening context openingResult).1
      split at result
      · exact ⟨openingToken, openingFound,
          (closeDelimited_startsAtOpening openingToken closing context []
            result).symm⟩
      · cases elementResult : element afterOpening with
        | ok value afterElement =>
            simp only [elementResult] at result
            split at result
            · exact ⟨openingToken, openingFound,
                (afterDelimitedElement_startsAtOpening element closing
                  allowTrailing context phase openingToken
                  (afterOpening.remainingCount + 1) [value] afterElement
                  values next result).symm⟩
            · contradiction
        | reject failure rejected =>
            simp only [elementResult] at result
            contradiction
        | invariant error =>
            simp only [elementResult] at result
            contradiction
  | reject failure rejected =>
      simp only [openingResult] at result
      contradiction
  | invariant error =>
      simp only [openingResult] at result
      contradiction

theorem delimited_startsAtCurrentTokenOnSuccess {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase) :
    Parser.StartsAtCurrentTokenOnSuccess
      (delimited opening closing allowEmpty element context phase)
        (·.span) :=
  delimitedWithPolicy_startsAtCurrentTokenOnSuccess opening closing allowEmpty
    true element context phase

theorem delimitedNoTrailing_startsAtCurrentTokenOnSuccess {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase) :
    Parser.StartsAtCurrentTokenOnSuccess
      (delimitedNoTrailing opening closing allowEmpty element context phase)
        (·.span) :=
  delimitedWithPolicy_startsAtCurrentTokenOnSuccess opening closing allowEmpty
    false element context phase

private theorem closeDelimited_cursor_lt_onSuccess {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List α) {input next : State} {values : DelimitedList α}
    (result : closeDelimited opening closing context elementsRev input =
      .ok values next) :
    input.cursor < next.cursor := by
  unfold closeDelimited at result
  cases closingResult : symbol closing context input with
  | ok token afterClosing =>
      simp only [closingResult] at result
      cases result
      rw [(symbol_ok_state_shape closing context closingResult).2]
      simp
  | reject failure rejected =>
      simp only [closingResult] at result
      contradiction
  | invariant error =>
      simp only [closingResult] at result
      contradiction

private theorem afterDelimitedElement_cursor_lt_onSuccess {α : Type}
    (element : Parser α) (closing : Symbol) (allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev input values next,
      afterDelimitedElement element closing allowTrailing context phase opening
          fuel elementsRev input = .ok values next →
        input.cursor < next.cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input values next result
      simp only [afterDelimitedElement] at result
      contradiction
  | succ fuel inductionHypothesis =>
      intro elementsRev input values next result
      unfold afterDelimitedElement at result
      split at result
      · cases commaResult : symbol .comma context input with
        | ok comma afterComma =>
            simp only [commaResult] at result
            have commaProgress : input.cursor < afterComma.cursor := by
              rw [(symbol_ok_state_shape .comma context commaResult).2]
              simp
            split at result
            · exact Nat.lt_trans commaProgress
                (closeDelimited_cursor_lt_onSuccess opening closing context
                  elementsRev result)
            · cases elementResult : element afterComma with
              | ok value afterElement =>
                  simp only [elementResult] at result
                  split at result
                  · exact Nat.lt_trans commaProgress
                      (Nat.lt_trans (by assumption)
                        (inductionHypothesis (value :: elementsRev) afterElement
                          values next result))
                  · contradiction
              | reject failure rejected =>
                  simp only [elementResult] at result
                  contradiction
              | invariant error =>
                  simp only [elementResult] at result
                  contradiction
        | reject failure rejected =>
            simp only [commaResult] at result
            contradiction
        | invariant error =>
            simp only [commaResult] at result
            contradiction
      · split at result
        · exact closeDelimited_cursor_lt_onSuccess opening closing context
            elementsRev result
        · unfold rejectAt at result
          contradiction

/-- A successful delimited parser consumes at least its opening and closing tokens. -/
theorem delimitedWithPolicy_cursor_lt_onSuccess {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase)
    {input next : State} {values : DelimitedList α}
    (result : delimitedWithPolicy opening closing allowEmpty allowTrailing
      element context phase input = .ok values next) :
    input.cursor < next.cursor := by
  unfold delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | ok openingToken afterOpening =>
      simp only [openingResult] at result
      have openingProgress : input.cursor < afterOpening.cursor := by
        rw [(symbol_ok_state_shape opening context openingResult).2]
        simp
      split at result
      · exact Nat.lt_trans openingProgress
          (closeDelimited_cursor_lt_onSuccess openingToken closing context []
            result)
      · cases elementResult : element afterOpening with
        | ok value afterElement =>
            simp only [elementResult] at result
            split at result
            · exact Nat.lt_trans openingProgress
                (Nat.lt_trans (by assumption)
                  (afterDelimitedElement_cursor_lt_onSuccess element closing
                    allowTrailing context phase openingToken
                    (afterOpening.remainingCount + 1) [value] afterElement
                    values next result))
            · contradiction
        | reject failure rejected =>
            simp only [elementResult] at result
            contradiction
        | invariant error =>
            simp only [elementResult] at result
            contradiction
  | reject failure rejected =>
      simp only [openingResult] at result
      contradiction
  | invariant error =>
      simp only [openingResult] at result
      contradiction

theorem delimitedWithPolicy_cursorMonotoneOnSuccess {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase) :
    Parser.CursorMonotoneOnSuccess
      (delimitedWithPolicy opening closing allowEmpty allowTrailing element
        context phase) := by
  intro input values next result
  exact Nat.le_of_lt (delimitedWithPolicy_cursor_lt_onSuccess opening closing
    allowEmpty allowTrailing element context phase result)

theorem delimited_cursorMonotoneOnSuccess {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase) :
    Parser.CursorMonotoneOnSuccess
      (delimited opening closing allowEmpty element context phase) :=
  delimitedWithPolicy_cursorMonotoneOnSuccess opening closing allowEmpty true
    element context phase

theorem delimitedNoTrailing_cursorMonotoneOnSuccess {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase) :
    Parser.CursorMonotoneOnSuccess
      (delimitedNoTrailing opening closing allowEmpty element context phase) :=
  delimitedWithPolicy_cursorMonotoneOnSuccess opening closing allowEmpty false
    element context phase

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DiagnosticReflectionProperties
/-! Backward propagation of diagnostic-free parser success. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace Parser

/-- A successful diagnostic-free output implies a diagnostic-free input. -/
def ReflectsDiagnosticFreeOnSuccess {alpha : Type}
    (parser : Parser alpha) : Prop :=
  ∀ input value next, parser input = .ok value next →
    next.diagnosticsRev = [] → input.diagnosticsRev = []

/-- Pure parsing reflects diagnostic freedom exactly. -/
theorem pure_reflectsDiagnosticFreeOnSuccess {alpha : Type}
    (value : alpha) :
    ReflectsDiagnosticFreeOnSuccess (pure value : Parser alpha) := by
  intro input result next parsed diagnosticFree
  cases parsed
  exact diagnosticFree

/-- Sequential composition reflects through both successful stages. -/
theorem bind_reflectsDiagnosticFreeOnSuccess {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    (firstReflects : ReflectsDiagnosticFreeOnSuccess first)
    (nextReflects : ∀ value, ReflectsDiagnosticFreeOnSuccess (next value)) :
    ReflectsDiagnosticFreeOnSuccess (first >>= next) := by
  intro input value final parsed diagnosticFree
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      have afterFree := nextReflects firstValue afterFirst value final parsed
        diagnosticFree
      exact firstReflects input firstValue afterFirst firstResult afterFree
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- Transactional ordered choice reflects through its successful branch. -/
theorem orElse_reflectsDiagnosticFreeOnSuccess {alpha : Type}
    {first second : Parser alpha}
    (firstReflects : ReflectsDiagnosticFreeOnSuccess first)
    (secondReflects : ReflectsDiagnosticFreeOnSuccess second) :
    ReflectsDiagnosticFreeOnSuccess (orElse first second) := by
  intro input value next parsed diagnosticFree
  unfold orElse at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      simp only [firstResult] at parsed
      cases parsed
      exact firstReflects input value next firstResult diagnosticFree
  | reject failure rejected =>
      simp only [firstResult] at parsed
      exact secondReflects input value next parsed diagnosticFree
  | invariant error => simp [firstResult] at parsed

end Parser

/-- Reading state reflects diagnostic freedom. -/
theorem getState_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess getState := by
  intro input value next parsed diagnosticFree
  unfold getState at parsed
  cases parsed
  exact diagnosticFree

/-- Exact token acceptance never removes prior diagnostics. -/
theorem acceptToken_reflectsDiagnosticFreeOnSuccess
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (acceptToken expected context accepts) := by
  intro input value next parsed diagnosticFree
  unfold acceptToken at parsed
  cases found : input.peek? with
  | none => simp [found, rejectAt] at parsed
  | some token =>
      simp only [found] at parsed
      split at parsed
      · cases parsed
        exact diagnosticFree
      · unfold rejectAt at parsed
        contradiction

theorem keyword_reflectsDiagnosticFreeOnSuccess
    (value : HardKeyword) (context : ParseContext) :
    Parser.ReflectsDiagnosticFreeOnSuccess (keyword value context) :=
  acceptToken_reflectsDiagnosticFreeOnSuccess (.keyword value) context
    (fun kind => kind == .keyword value)

theorem symbol_reflectsDiagnosticFreeOnSuccess
    (value : Symbol) (context : ParseContext) :
    Parser.ReflectsDiagnosticFreeOnSuccess (symbol value context) :=
  acceptToken_reflectsDiagnosticFreeOnSuccess (.symbol value) context
    (fun kind => kind == .symbol value)

theorem contextual_reflectsDiagnosticFreeOnSuccess
    (value : ContextualKeyword) (context : ParseContext) :
    Parser.ReflectsDiagnosticFreeOnSuccess (contextual value context) :=
  acceptToken_reflectsDiagnosticFreeOnSuccess (.contextual value) context
    (fun kind => kind.isContextual value)

/-- Raw identifiers never remove prior diagnostics. -/
theorem rawIdentifier_reflectsDiagnosticFreeOnSuccess
    (context : ParseContext) :
    Parser.ReflectsDiagnosticFreeOnSuccess (rawIdentifier context) := by
  intro input value next parsed diagnosticFree
  rw [rawIdentifier_ok_state_shape context parsed] at diagnosticFree
  exact diagnosticFree

/-- Checked identifiers may add a diagnostic but never remove one. -/
theorem identifier_reflectsDiagnosticFreeOnSuccess
    (context : ParseContext) :
    Parser.ReflectsDiagnosticFreeOnSuccess (identifier context) := by
  intro input value next parsed diagnosticFree
  unfold identifier at parsed
  cases rawResult : rawIdentifier context input with
  | invariant error => simp [rawResult] at parsed
  | reject failure rejected => simp [rawResult] at parsed
  | ok name afterName =>
      simp only [rawResult] at parsed
      split at parsed
      · cases parsed
        simp [State.emit] at diagnosticFree
      · cases parsed
        exact rawIdentifier_reflectsDiagnosticFreeOnSuccess context input value
          next rawResult diagnosticFree

/-- Emitting a diagnostic cannot have a diagnostic-free success. -/
theorem emitDiagnostic_reflectsDiagnosticFreeOnSuccess
    (diagnostic : ParseDiagnostic) :
    Parser.ReflectsDiagnosticFreeOnSuccess (emitDiagnostic diagnostic) := by
  intro input value next parsed diagnosticFree
  unfold emitDiagnostic modifyState at parsed
  cases parsed
  simp [State.emit] at diagnosticFree

private theorem closeDelimited_reflectsDiagnosticFreeOnSuccess {alpha : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext)
    (elementsRev : List alpha) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (closeDelimited opening closing context elementsRev) := by
  intro input values next parsed diagnosticFree
  unfold closeDelimited at parsed
  cases closingResult : symbol closing context input with
  | invariant error => simp [closingResult] at parsed
  | reject failure rejected => simp [closingResult] at parsed
  | ok token afterClosing =>
      simp only [closingResult] at parsed
      cases parsed
      exact symbol_reflectsDiagnosticFreeOnSuccess closing context input token
        next closingResult diagnosticFree

private theorem afterDelimitedElement_reflectsDiagnosticFreeOnSuccess
    {alpha : Type} (element : Parser alpha)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element)
    (closing : Symbol) (allowTrailing : Bool) (context : ParseContext)
    (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (afterDelimitedElement element closing allowTrailing context phase
          opening fuel elementsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro elementsRev input values next parsed diagnosticFree
      simp [afterDelimitedElement] at parsed
  | succ fuel inductionHypothesis =>
      intro elementsRev input values next parsed diagnosticFree
      unfold afterDelimitedElement at parsed
      split at parsed
      · cases commaResult : symbol .comma context input with
        | invariant error => simp [commaResult] at parsed
        | reject failure rejected => simp [commaResult] at parsed
        | ok comma afterComma =>
            simp only [commaResult] at parsed
            split at parsed
            · have afterCommaFree :=
                  closeDelimited_reflectsDiagnosticFreeOnSuccess opening
                    closing context elementsRev afterComma values next parsed
                    diagnosticFree
              exact symbol_reflectsDiagnosticFreeOnSuccess .comma context
                input comma afterComma commaResult afterCommaFree
            · cases elementResult : element afterComma with
              | invariant error => simp [elementResult] at parsed
              | reject failure rejected => simp [elementResult] at parsed
              | ok elementValue afterElement =>
                  simp only [elementResult] at parsed
                  split at parsed
                  · have afterElementFree := inductionHypothesis
                        (elementValue :: elementsRev) afterElement values next
                        parsed diagnosticFree
                    have afterCommaFree := elementReflects afterComma
                      elementValue afterElement elementResult afterElementFree
                    exact symbol_reflectsDiagnosticFreeOnSuccess .comma context
                      input comma afterComma commaResult afterCommaFree
                  · contradiction
      · split at parsed
        · exact closeDelimited_reflectsDiagnosticFreeOnSuccess opening
            closing context elementsRev input values next parsed diagnosticFree
        · unfold rejectAt at parsed
          contradiction

/-- Generic delimiter policy never removes diagnostics from its input. -/
theorem delimitedWithPolicy_reflectsDiagnosticFreeOnSuccess {alpha : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser alpha) (context : ParseContext) (phase : ParserPhase)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (delimitedWithPolicy opening closing allowEmpty allowTrailing element
        context phase) := by
  intro input values next parsed diagnosticFree
  unfold delimitedWithPolicy at parsed
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok openingToken afterOpening =>
      simp only [openingResult] at parsed
      split at parsed
      · have afterOpeningFree :=
            closeDelimited_reflectsDiagnosticFreeOnSuccess openingToken
              closing context [] afterOpening values next parsed diagnosticFree
        exact symbol_reflectsDiagnosticFreeOnSuccess opening context input
          openingToken afterOpening openingResult afterOpeningFree
      · cases elementResult : element afterOpening with
        | invariant error => simp [elementResult] at parsed
        | reject failure rejected => simp [elementResult] at parsed
        | ok value afterElement =>
            simp only [elementResult] at parsed
            split at parsed
            · have afterElementFree :=
                  afterDelimitedElement_reflectsDiagnosticFreeOnSuccess
                    element elementReflects closing allowTrailing context phase
                    openingToken (afterOpening.remainingCount + 1) [value]
                    afterElement values next parsed diagnosticFree
              have afterOpeningFree := elementReflects afterOpening value
                afterElement elementResult afterElementFree
              exact symbol_reflectsDiagnosticFreeOnSuccess opening context
                input openingToken afterOpening openingResult afterOpeningFree
            · contradiction

theorem delimited_reflectsDiagnosticFreeOnSuccess {alpha : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser alpha)
    (context : ParseContext) (phase : ParserPhase)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (delimited opening closing allowEmpty element context phase) :=
  delimitedWithPolicy_reflectsDiagnosticFreeOnSuccess opening closing
    allowEmpty true element context phase elementReflects

theorem delimitedNoTrailing_reflectsDiagnosticFreeOnSuccess {alpha : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser alpha)
    (context : ParseContext) (phase : ParserPhase)
    (elementReflects : Parser.ReflectsDiagnosticFreeOnSuccess element) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (delimitedNoTrailing opening closing allowEmpty element context phase) :=
  delimitedWithPolicy_reflectsDiagnosticFreeOnSuccess opening closing
    allowEmpty false element context phase elementReflects

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeclarativePrimitiveProperties
/-! Primitive bridges from parser success to exact declarative tokens. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace State

/-- Forget parser-only state while retaining the active grammar remainder. -/
def declarativeRemainder (state : State) : DeclarativeGrammar.Remainder := {
  tokens := state.tokens
  endIndex := state.window.endIndex
  cursor := state.cursor
}

end State

/-- A successful current-token lookup is an exact declarative token. -/
theorem tokenAt_of_peek?_eq_some {input : State} {token : Token}
    (found : input.peek? = some token) :
    DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor token :=
  ⟨State.cursor_lt_endIndex_of_peek?_eq_some found,
    State.getElem?_eq_some_of_peek?_eq_some found⟩

/-- A failed symbol lookahead excludes that symbol at the grammar cursor. -/
theorem symbolAbsentAt_of_isSymbol_eq_false (value : Symbol)
    {input : State} (absent : isSymbol input value = false) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor (.symbol value) := by
  rintro ⟨span, inside, found⟩
  unfold isSymbol State.peekKind? State.peek? at absent
  simp only [inside, ↓reduceIte, found, Option.map_some] at absent
  change instBEqTokenKind.beq (.symbol value) (.symbol value) = false at absent
  simp only [instBEqTokenKind.beq] at absent
  change instBEqSymbol.beq value value = false at absent
  unfold instBEqSymbol.beq at absent
  cases value <;> contradiction

/-- A failed keyword lookahead excludes that keyword at the grammar cursor. -/
theorem keywordAbsentAt_of_isKeyword_eq_false (value : HardKeyword)
    {input : State} (absent : isKeyword input value = false) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor (.keyword value) := by
  rintro ⟨span, inside, found⟩
  unfold isKeyword State.peekKind? State.peek? at absent
  simp only [inside, ↓reduceIte, found, Option.map_some] at absent
  change instBEqTokenKind.beq (.keyword value) (.keyword value) = false at absent
  simp only [instBEqTokenKind.beq] at absent
  change instBEqHardKeyword.beq value value = false at absent
  unfold instBEqHardKeyword.beq at absent
  cases value <;> contradiction

/-- Failed contextual lookahead excludes its identifier spelling. -/
theorem contextualAbsentAt_of_isContextual_eq_false
    (value : ContextualKeyword) {input : State}
    (absent : isContextual input value = false) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor (.identifier value.spelling) := by
  rintro ⟨span, inside, found⟩
  unfold isContextual State.peekKind? State.peek? at absent
  simp only [inside, ↓reduceIte, found, Option.map_some,
    TokenKind.isContextual] at absent
  have same : (value.spelling == value.spelling) = true :=
    beq_iff_eq.mpr rfl
  rw [same] at absent
  contradiction

private theorem acceptToken_ok_tokenAt_of_kind (kind : TokenKind)
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool)
    (acceptsKind : ∀ actual, accepts actual = true → actual = kind)
    {input next : State} {token : Token}
    (result : acceptToken expected context accepts input =
      .ok token next) :
    DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor {
      span := token.span
      value := kind
    } ∧ next = { input with cursor := input.cursor + 1 } := by
  unfold acceptToken at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some current =>
      simp only [found] at result
      split at result
      next accepted =>
        have kindEq : current.value = kind := acceptsKind current.value accepted
        cases result
        have tokenEq : token = { span := token.span, value := kind } := by
          rcases token with ⟨span, value⟩
          simp only at kindEq ⊢
          subst value
          rfl
        rw [← tokenEq]
        exact ⟨tokenAt_of_peek?_eq_some found, rfl⟩
      next rejected =>
        unfold rejectAt at result
        contradiction

private theorem keyword_accepts_kind (value : HardKeyword)
    {actual : TokenKind}
    (accepted : (actual == .keyword value) = true) :
    actual = .keyword value := by
  change instBEqTokenKind.beq actual (.keyword value) = true at accepted
  cases actual <;> simp only [instBEqTokenKind.beq] at accepted
  all_goals try { contradiction }
  case keyword actual =>
    change instBEqHardKeyword.beq actual value = true at accepted
    unfold instBEqHardKeyword.beq at accepted
    cases actual <;> cases value <;>
      first | rfl | cases accepted

/-- Keyword success exposes the exact located keyword token consumed. -/
theorem keyword_ok_tokenAt (value : HardKeyword) (context : ParseContext)
    {input next : State} {token : Token}
    (result : keyword value context input = .ok token next) :
    DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor {
      span := token.span
      value := .keyword value
    } ∧ next = { input with cursor := input.cursor + 1 } :=
  acceptToken_ok_tokenAt_of_kind (.keyword value) (.keyword value) context
    (· == .keyword value)
    (fun actual accepted =>
      keyword_accepts_kind value (actual := actual) accepted) result

private theorem symbol_accepts_kind (value : Symbol) {actual : TokenKind}
    (accepted : (actual == .symbol value) = true) :
    actual = .symbol value := by
  change instBEqTokenKind.beq actual (.symbol value) = true at accepted
  cases actual <;> simp only [instBEqTokenKind.beq] at accepted
  all_goals try { contradiction }
  case symbol actual =>
    change instBEqSymbol.beq actual value = true at accepted
    unfold instBEqSymbol.beq at accepted
    cases actual <;> cases value <;>
      first | rfl | cases accepted

/-- Symbol success exposes the exact located symbol token consumed. -/
theorem symbol_ok_tokenAt (value : Symbol) (context : ParseContext)
    {input next : State} {token : Token}
    (result : symbol value context input = .ok token next) :
    DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor {
      span := token.span
      value := .symbol value
    } ∧ next = { input with cursor := input.cursor + 1 } :=
  acceptToken_ok_tokenAt_of_kind (.symbol value) (.symbol value) context
    (· == .symbol value)
    (fun actual accepted =>
      symbol_accepts_kind value (actual := actual) accepted) result

private theorem contextual_accepts_kind (value : ContextualKeyword)
    {actual : TokenKind} (accepted : actual.isContextual value = true) :
    actual = .identifier value.spelling := by
  cases actual <;> simp only [TokenKind.isContextual] at accepted
  all_goals try { contradiction }
  case identifier text =>
    have equal : text = value.spelling := beq_iff_eq.mp accepted
    subst text
    rfl

/-- Contextual-keyword success exposes its exact identifier token. -/
theorem contextual_ok_tokenAt (value : ContextualKeyword)
    (context : ParseContext) {input next : State} {token : Token}
    (result : contextual value context input = .ok token next) :
    DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor {
      span := token.span
      value := .identifier value.spelling
    } ∧ next = { input with cursor := input.cursor + 1 } :=
  acceptToken_ok_tokenAt_of_kind (.identifier value.spelling)
    (.contextual value) context (fun kind => kind.isContextual value)
    (fun actual accepted =>
      contextual_accepts_kind value (actual := actual) accepted) result

/-- Raw identifier success exposes the exact identifier token consumed. -/
theorem rawIdentifier_ok_tokenAt (context : ParseContext)
    {input next : State} {name : Identifier}
    (result : rawIdentifier context input = .ok name next) :
    DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor {
      span := name.span
      value := .identifier name.value
    } ∧ next = { input with cursor := input.cursor + 1 } := by
  unfold rawIdentifier at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case identifier text =>
        cases result
        exact ⟨⟨State.cursor_lt_endIndex_of_peek?_eq_some found,
          State.getElem?_eq_some_of_peek?_eq_some found⟩, rfl⟩

/-- Checked identifier success retains the exact token despite diagnostics. -/
theorem identifier_ok_tokenAt (context : ParseContext)
    {input next : State} {name : Identifier}
    (result : identifier context input = .ok name next) :
    DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor {
      span := name.span
      value := .identifier name.value
    } ∧ next.tokens = input.tokens ∧ next.window = input.window ∧
      next.cursor = input.cursor + 1 := by
  unfold identifier at result
  cases raw : rawIdentifier context input with
  | invariant error => simp [raw] at result
  | reject failure rejected => simp [raw] at result
  | ok parsed afterName =>
      have rawSound := rawIdentifier_ok_tokenAt context raw
      simp only [raw] at result
      split at result <;> cases result
      · rw [rawSound.2]
        exact ⟨rawSound.1, by simp [State.emit],
          by simp [State.emit], by simp [State.emit]⟩
      · rw [rawSound.2]
        exact ⟨rawSound.1, rfl, rfl, rfl⟩

/-- Checked identifier success follows the parser-independent identifier grammar. -/
theorem identifier_success_sound (context : ParseContext)
    {input next : State} {name : Identifier}
    (result : identifier context input = .ok name next) :
    DeclarativeGrammar.IdentifierParses input.declarativeRemainder name
      next.declarativeRemainder := by
  rcases identifier_ok_tokenAt context result with
    ⟨nameToken, tokensEq, windowEq, cursorEq⟩
  exact ⟨nameToken, tokensEq,
    congrArg TokenWindow.endIndex windowEq, cursorEq⟩

/-- Keyword success is one exact parser-independent token transition. -/
theorem keyword_success_exactTokenParses
    (value : HardKeyword) (context : ParseContext)
    {input next : State} {token : Token}
    (result : keyword value context input = .ok token next) :
    DeclarativeGrammar.ExactTokenParses (.keyword value)
      input.declarativeRemainder token.span next.declarativeRemainder := by
  rcases keyword_ok_tokenAt value context result with ⟨tokenAt, shape⟩
  unfold DeclarativeGrammar.ExactTokenParses
  refine ⟨tokenAt, ?_⟩
  rw [shape]
  rfl

/-- Symbol success is one exact parser-independent token transition. -/
theorem symbol_success_exactTokenParses
    (value : Symbol) (context : ParseContext)
    {input next : State} {token : Token}
    (result : symbol value context input = .ok token next) :
    DeclarativeGrammar.ExactTokenParses (.symbol value)
      input.declarativeRemainder token.span next.declarativeRemainder := by
  rcases symbol_ok_tokenAt value context result with ⟨tokenAt, shape⟩
  unfold DeclarativeGrammar.ExactTokenParses
  refine ⟨tokenAt, ?_⟩
  rw [shape]
  rfl

/-- Contextual-keyword success is one exact token transition. -/
theorem contextual_success_exactTokenParses
    (value : ContextualKeyword) (context : ParseContext)
    {input next : State} {token : Token}
    (result : contextual value context input = .ok token next) :
    DeclarativeGrammar.ExactTokenParses (.identifier value.spelling)
      input.declarativeRemainder token.span next.declarativeRemainder := by
  rcases contextual_ok_tokenAt value context result with ⟨tokenAt, shape⟩
  unfold DeclarativeGrammar.ExactTokenParses
  refine ⟨tokenAt, ?_⟩
  rw [shape]
  rfl

end Solcore.Syntax.Parser
end
