import Solcore.Syntax.Parser.State
import Init.Data.List.Nat.Pairwise

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace State

/-- A successful current-token lookup is the array lookup at the cursor. -/
theorem getElem?_eq_some_of_peek?_eq_some {state : State} {token : Token}
    (found : state.peek? = some token) :
    state.tokens[state.cursor]? = some token := by
  unfold peek? at found
  split at found
  · exact found
  · contradiction

/-- A successful lookahead is the array lookup at `cursor + offset`. -/
theorem getElem?_eq_some_of_peekOffset?_eq_some {state : State}
    {offset : Nat} {token : Token}
    (found : state.peekOffset? offset = some token) :
    state.tokens[state.cursor + offset]? = some token := by
  change (if state.cursor + offset < state.window.endIndex then
    state.tokens[state.cursor + offset]? else none) = some token at found
  split at found
  · exact found
  · contradiction

/-- A successful lookahead index is inside the active parser window. -/
theorem cursor_add_lt_endIndex_of_peekOffset?_eq_some {state : State}
    {offset : Nat} {token : Token}
    (found : state.peekOffset? offset = some token) :
    state.cursor + offset < state.window.endIndex := by
  change (if state.cursor + offset < state.window.endIndex then
    state.tokens[state.cursor + offset]? else none) = some token at found
  split at found
  · assumption
  · contradiction

/-- A present current token determines `currentSpan` exactly. -/
theorem currentSpan_eq_span_of_peek?_eq_some {state : State} {token : Token}
    (found : state.peek? = some token) :
    state.currentSpan = token.span := by
  simp only [currentSpan, found]

/-- After one advance, the new current token is the old one-token lookahead. -/
theorem peek?_eq_peekOffset?_one_of_advance? {state next : State}
    {token : Token} (advanced : state.advance? = some (token, next)) :
    next.peek? = state.peekOffset? 1 := by
  unfold advance? at advanced
  cases found : state.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      rfl

namespace ValidFor

private theorem token_mem_of_getElem?_eq_some {state : State}
    {index : Nat} {token : Token}
    (found : state.tokens[index]? = some token) :
    token ∈ state.tokens.toList := by
  rcases Array.getElem?_eq_some_iff.mp found with ⟨bound, equation⟩
  apply Array.mem_toList_iff.mpr
  rw [← equation]
  exact Array.getElem_mem bound

/-- Every token retrievable from a valid state's immutable input is source-valid. -/
theorem token_span_validFor_of_getElem?_eq_some {state : State}
    (valid : state.ValidFor) {index : Nat} {token : Token}
    (found : state.tokens[index]? = some token) :
    token.span.ValidFor state.file :=
  valid.tokens.span_valid (token_mem_of_getElem?_eq_some found)

/-- Every token retrievable from a valid state has a nonempty span. -/
theorem token_span_nonempty_of_getElem?_eq_some {state : State}
    (valid : state.ValidFor) {index : Nat} {token : Token}
    (found : state.tokens[index]? = some token) :
    token.span.startByte < token.span.endByte :=
  valid.tokens.span_nonempty (token_mem_of_getElem?_eq_some found)

/-- Array index order in a valid state implies source-span nonoverlap. -/
theorem token_end_le_token_start_of_getElem?_lt {state : State}
    (valid : state.ValidFor) {earlierIndex laterIndex : Nat}
    {earlier later : Token}
    (earlierFound : state.tokens[earlierIndex]? = some earlier)
    (laterFound : state.tokens[laterIndex]? = some later)
    (before : earlierIndex < laterIndex) :
    earlier.span.endByte ≤ later.span.startByte := by
  rcases Array.getElem?_eq_some_iff.mp earlierFound with
    ⟨earlierBound, earlierEquation⟩
  rcases Array.getElem?_eq_some_iff.mp laterFound with
    ⟨laterBound, laterEquation⟩
  have ordered :=
    List.pairwise_iff_getElem.mp valid.tokens.pairwise_nonoverlap
      earlierIndex laterIndex
      (by simpa using earlierBound)
      (by simpa using laterBound)
      before
  simpa only [Array.getElem_toList, earlierEquation, laterEquation] using ordered

/-- Every token returned by bounded lookahead has valid source provenance. -/
theorem peekOffset?_span_validFor {state : State} (valid : state.ValidFor)
    {offset : Nat} {token : Token}
    (found : state.peekOffset? offset = some token) :
    token.span.ValidFor state.file :=
  valid.token_span_validFor_of_getElem?_eq_some
    (getElem?_eq_some_of_peekOffset?_eq_some found)

/-- Every token returned by bounded lookahead has a nonempty source span. -/
theorem peekOffset?_span_nonempty {state : State} (valid : state.ValidFor)
    {offset : Nat} {token : Token}
    (found : state.peekOffset? offset = some token) :
    token.span.startByte < token.span.endByte :=
  valid.token_span_nonempty_of_getElem?_eq_some
    (getElem?_eq_some_of_peekOffset?_eq_some found)

/-- Every remaining lookahead token starts after each already-consumed token. -/
theorem consumed_end_le_peekOffset_start {state : State}
    (valid : state.ValidFor) {consumedIndex offset : Nat}
    {consumed remaining : Token}
    (consumedFound : state.tokens[consumedIndex]? = some consumed)
    (consumedBeforeCursor : consumedIndex < state.cursor)
    (remainingFound : state.peekOffset? offset = some remaining) :
    consumed.span.endByte ≤ remaining.span.startByte := by
  apply valid.token_end_le_token_start_of_getElem?_lt consumedFound
    (getElem?_eq_some_of_peekOffset?_eq_some remainingFound)
  exact Nat.lt_of_lt_of_le consumedBeforeCursor
    (Nat.le_add_right state.cursor offset)

/-- The token consumed by `advance?` ends before the next present token starts. -/
theorem consumed_end_le_peek_start_after_advance {state next : State}
    (valid : state.ValidFor) {consumed following : Token}
    (advanced : state.advance? = some (consumed, next))
    (followingFound : next.peek? = some following) :
    consumed.span.endByte ≤ following.span.startByte := by
  unfold advance? at advanced
  cases currentFound : state.peek? with
  | none => simp [currentFound] at advanced
  | some current =>
      simp only [currentFound, Option.map_some] at advanced
      cases advanced
      have laterFound : state.tokens[state.cursor + 1]? = some following := by
        simpa using
          (getElem?_eq_some_of_peek?_eq_some (state := {
            state with cursor := state.cursor + 1 }) followingFound)
      apply valid.token_end_le_token_start_of_getElem?_lt
        (getElem?_eq_some_of_peek?_eq_some currentFound)
        laterFound
      simp

/-- With a next token present, the consumed span ends before the new current span. -/
theorem consumed_end_le_currentSpan_start_after_advance {state next : State}
    (valid : state.ValidFor) {consumed following : Token}
    (advanced : state.advance? = some (consumed, next))
    (followingFound : next.peek? = some following) :
    consumed.span.endByte ≤ next.currentSpan.startByte := by
  rw [currentSpan_eq_span_of_peek?_eq_some followingFound]
  exact valid.consumed_end_le_peek_start_after_advance advanced followingFound

end ValidFor

end State

end Solcore.Syntax.Parser
