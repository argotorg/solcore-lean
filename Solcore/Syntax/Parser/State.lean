import Solcore.Syntax.Parser.Result
import Solcore.Syntax.SpanSequence
import Init.Data.List.Nat.Pairwise

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Exclusive token and byte boundary of one parser subwindow. -/
structure TokenWindow where
  endIndex : Nat
  endByte : Nat
  deriving Repr, BEq, DecidableEq

/-- Immutable input plus the cursor and reverse diagnostic accumulator. -/
structure State where
  file : SourceFile
  tokens : Array Token
  cursor : Nat
  window : TokenWindow
  diagnosticsRev : List ParseDiagnostic := []
  deriving Repr, BEq

namespace State

/-- Declarative invariants required by every canonical parser state. -/
structure ValidFor (state : State) : Prop where
  tokens : SpanSequence.ValidFor state.file
    (fun token : Token => token.span) 0 state.tokens.toList
  cursor_le_endIndex : state.cursor ≤ state.window.endIndex
  endIndex_le_size : state.window.endIndex ≤ state.tokens.size
  endByte_le_source :
    state.window.endByte ≤ state.file.content.utf8ByteSize
  endByte_boundary :
    isUtf8Boundary state.file.content state.window.endByte = true
  diagnosticsRev : ∀ diagnostic ∈ state.diagnosticsRev,
    diagnostic.span.ValidFor state.file

/-- Root token window produced by canonical lexical analysis. -/
def initial (file : SourceFile) (lexed : LexedFile) : State := {
  file
  tokens := lexed.tokens.toArray
  cursor := 0
  window := {
    endIndex := lexed.tokens.length
    endByte := file.content.utf8ByteSize
  }
}

/-- Executable bounds check for a root or captured parser window. -/
def windowIsValid (state : State) : Bool :=
  state.cursor ≤ state.window.endIndex &&
    state.window.endIndex ≤ state.tokens.size &&
    state.window.endByte ≤ state.file.content.utf8ByteSize &&
    isUtf8Boundary state.file.content state.window.endByte

/-- Current token when the cursor is inside the active window. -/
def peek? (state : State) : Option Token :=
  if state.cursor < state.window.endIndex then
    state.tokens[state.cursor]?
  else
    none

def peekKind? (state : State) : Option TokenKind :=
  state.peek?.map (·.value)

/-- Look ahead within the active window without changing the cursor. -/
def peekOffset? (state : State) (offset : Nat) : Option Token :=
  let index := state.cursor + offset
  if index < state.window.endIndex then
    state.tokens[index]?
  else
    none

def peekOffsetKind? (state : State) (offset : Nat) : Option TokenKind :=
  (state.peekOffset? offset).map (·.value)

def atEnd (state : State) : Bool :=
  state.cursor ≥ state.window.endIndex

/-- Empty failure span at a window end, or the current token span. -/
def currentSpan (state : State) : SourceSpan :=
  match state.peek? with
  | some token => token.span
  | none => Lexer.sourceSpan state.file state.window.endByte state.window.endByte

/-- Number of tokens remaining in the active window. -/
def remainingCount (state : State) : Nat :=
  state.window.endIndex - state.cursor

/-- Consume one token inside the active window. -/
def advance? (state : State) : Option (Token × State) :=
  state.peek?.map fun token =>
    (token, { state with cursor := state.cursor + 1 })

/-- Append an ordinary diagnostic in constant time. -/
def emit (state : State) (diagnostic : ParseDiagnostic) : State :=
  { state with diagnosticsRev := diagnostic :: state.diagnosticsRev }

def diagnostics (state : State) : List ParseDiagnostic :=
  state.diagnosticsRev.reverse

private theorem token_mem_of_peek?_eq_some {state : State} {token : Token}
    (found : state.peek? = some token) : token ∈ state.tokens.toList := by
  unfold peek? at found
  split at found
  · have lookup : state.tokens[state.cursor]? = some token := found
    rcases Array.getElem?_eq_some_iff.mp lookup with ⟨bound, equation⟩
    apply Array.mem_toList_iff.mpr
    rw [← equation]
    exact Array.getElem_mem bound
  · contradiction

/-- A present current token belongs to the active window. -/
theorem cursor_lt_endIndex_of_peek?_eq_some {state : State} {token : Token}
    (found : state.peek? = some token) :
    state.cursor < state.window.endIndex := by
  unfold peek? at found
  split at found
  · assumption
  · contradiction

namespace ValidFor

/-- A token returned by `peek?` has valid provenance. -/
theorem peek?_span_validFor {state : State} (valid : state.ValidFor)
    {token : Token} (found : state.peek? = some token) :
    token.span.ValidFor state.file :=
  SpanSequence.ValidFor.span_valid valid.tokens
    (token_mem_of_peek?_eq_some found)

/-- The current token or empty window-end span is always source-valid. -/
theorem currentSpan_validFor {state : State} (valid : state.ValidFor) :
    state.currentSpan.ValidFor state.file := by
  unfold currentSpan
  cases found : state.peek? with
  | some token => exact valid.peek?_span_validFor found
  | none =>
      exact ⟨rfl, Nat.le_refl _, valid.endByte_le_source,
        valid.endByte_boundary, valid.endByte_boundary⟩

/-- Advancing one present token preserves all state invariants. -/
theorem advance?_validFor {state next : State} {token : Token}
    (valid : state.ValidFor)
    (advanced : state.advance? = some (token, next)) : next.ValidFor := by
  unfold advance? at advanced
  cases found : state.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      exact {
        tokens := valid.tokens
        cursor_le_endIndex :=
          Nat.succ_le_of_lt (cursor_lt_endIndex_of_peek?_eq_some found)
        endIndex_le_size := valid.endIndex_le_size
        endByte_le_source := valid.endByte_le_source
        endByte_boundary := valid.endByte_boundary
        diagnosticsRev := valid.diagnosticsRev
      }

/-- Emitting a valid diagnostic preserves all state invariants. -/
theorem emit_validFor {state : State} (valid : state.ValidFor)
    (diagnostic : ParseDiagnostic)
    (diagnosticValid : diagnostic.span.ValidFor state.file) :
    (state.emit diagnostic).ValidFor := by
  exact {
    tokens := valid.tokens
    cursor_le_endIndex := valid.cursor_le_endIndex
    endIndex_le_size := valid.endIndex_le_size
    endByte_le_source := valid.endByte_le_source
    endByte_boundary := valid.endByte_boundary
    diagnosticsRev := by
      intro retained member
      rcases List.mem_cons.mp member with rfl | member
      · exact diagnosticValid
      · exact valid.diagnosticsRev retained member
  }

/-- Every diagnostic exposed in written order retains a valid source span. -/
theorem diagnostics_span_validFor {state : State} (valid : state.ValidFor)
    {diagnostic : ParseDiagnostic} (member : diagnostic ∈ state.diagnostics) :
    diagnostic.span.ValidFor state.file := by
  apply valid.diagnosticsRev diagnostic
  simpa only [diagnostics, List.mem_reverse] using member

end ValidFor

/-- Enter a previously validated token subwindow. -/
def enterWindow (state : State) (startIndex : Nat)
    (window : TokenWindow) : State := {
  state with
  cursor := startIndex
  window
  diagnosticsRev := []
}

/-- Merge child diagnostics into a parent whose accumulator is reversed. -/
def mergeDiagnostics (parent child : State) : State :=
  { parent with
    diagnosticsRev := child.diagnosticsRev ++ parent.diagnosticsRev
  }

end State

/-- Uncommitted parser rejection; its caller selects the recovery policy. -/
structure Failure where
  span : SourceSpan
  found : Option TokenKind
  expected : NonemptyList ParseExpectation
  context : ParseContext
  deriving Repr, BEq, DecidableEq

namespace Failure

def toDiagnostic (failure : Failure) : ParseDiagnostic := {
  span := failure.span
  kind := .unexpected failure.found failure.expected failure.context
}

/-- Converting a failure to a diagnostic preserves its exact valid span. -/
theorem toDiagnostic_span_validFor {file : SourceFile} (failure : Failure)
    (valid : failure.span.ValidFor file) :
    failure.toDiagnostic.span.ValidFor file :=
  valid

end Failure

/-- Parser control result before a caller commits to recovery. -/
inductive Reply (α : Type) where
  | ok (value : α) (state : State)
  | reject (failure : Failure) (state : State)
  | invariant (error : ParserInvariantError)
  deriving Repr, BEq

abbrev Parser (α : Type) := State → Reply α

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.StateCursorProperties`
-/

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
