import Solcore

/-! External consumers for cursor-relative parser span guarantees. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example (state : State) (valid : state.ValidFor)
    (offset : Nat) (token : Token)
    (found : state.peekOffset? offset = some token) :
    token.span.ValidFor state.file :=
  valid.peekOffset?_span_validFor found

example (state : State) (valid : state.ValidFor)
    (consumedIndex offset : Nat) (consumed remaining : Token)
    (consumedFound : state.tokens[consumedIndex]? = some consumed)
    (consumedBeforeCursor : consumedIndex < state.cursor)
    (remainingFound : state.peekOffset? offset = some remaining) :
    consumed.span.endByte ≤ remaining.span.startByte :=
  valid.consumed_end_le_peekOffset_start consumedFound
    consumedBeforeCursor remainingFound

example (state next : State) (valid : state.ValidFor)
    (consumed following : Token)
    (advanced : state.advance? = some (consumed, next))
    (followingFound : next.peek? = some following) :
    consumed.span.endByte ≤ next.currentSpan.startByte :=
  valid.consumed_end_le_currentSpan_start_after_advance
    advanced followingFound

example (state next : State) (token : Token)
    (advanced : state.advance? = some (token, next)) :
    next.peek? = state.peekOffset? 1 :=
  State.peek?_eq_peekOffset?_one_of_advance? advanced

end Tests
