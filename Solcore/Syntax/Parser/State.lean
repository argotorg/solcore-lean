import Solcore.Syntax.Parser.Result

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

end Failure

/-- Parser control result before a caller commits to recovery. -/
inductive Reply (α : Type) where
  | ok (value : α) (state : State)
  | reject (failure : Failure) (state : State)
  | invariant (error : ParserInvariantError)
  deriving Repr, BEq

abbrev Parser (α : Type) := State → Reply α

end Solcore.Syntax.Parser
