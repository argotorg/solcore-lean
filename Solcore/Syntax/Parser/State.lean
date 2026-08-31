import Solcore.Syntax.Parser.Result

set_option autoImplicit false

namespace Solcore.Syntax

/-- Source-ordered, nonempty spans whose provenance is valid for one file. -/
def SpanSequence.ValidFor {α : Type} (file : SourceFile)
    (spanOf : α → SourceSpan) : Nat → List α → Prop
  | _, [] => True
  | previousEnd, item :: rest =>
      (spanOf item).ValidFor file ∧
        previousEnd ≤ (spanOf item).startByte ∧
        (spanOf item).startByte < (spanOf item).endByte ∧
        SpanSequence.ValidFor file spanOf (spanOf item).endByte rest

namespace SpanSequence.ValidFor

/-- Every member of a valid sequence has valid source provenance. -/
theorem span_valid {α : Type} {file : SourceFile}
    {spanOf : α → SourceSpan} {previousEnd : Nat} {items : List α}
    (valid : SpanSequence.ValidFor file spanOf previousEnd items)
    {item : α} (member : item ∈ items) :
    (spanOf item).ValidFor file := by
  induction items generalizing previousEnd with
  | nil => contradiction
  | cons head tail ih =>
      simp only [SpanSequence.ValidFor] at valid
      rcases valid with ⟨headValid, _afterPrevious, _nonempty, tailValid⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact headValid
      · exact ih tailValid member

end SpanSequence.ValidFor

end Solcore.Syntax

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
