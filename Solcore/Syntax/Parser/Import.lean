import Solcore.Syntax.Parser.Delimited
import Solcore.Syntax.Parser.ModulePath
import Solcore.Syntax.Parser.Operator
import Solcore.Syntax.Parser.TopLevel

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ImportInternals

/-- Parse the optional alias of one selected import. -/
def selectedAlias : Parser (Option Identifier) := do
  let state ← getState
  if isKeyword state .asKw then
    let _ ← keyword .asKw .importDecl
    let name ← identifier .importDecl
    pure (some name)
  else
    pure none

end ImportInternals

/-- Parse one selector and its optional local alias. -/
def selectedImport : Parser SelectedImport := do
  let source ← selectorName .importDecl
  let alias ← ImportInternals.selectedAlias
  let span := match alias with
    | some name => SourceSpan.cover source.span name.span
    | none => source.span
  pure {
    span
    value := { source, alias }
  }

namespace ImportInternals

/-- Require at least one selected import. -/
def requireSelected (values : DelimitedList SelectedImport) :
    Parser (NonemptyDelimitedList SelectedImport) :=
  match values.elements with
  | head :: tail => pure {
      span := values.span
      elements := { head, tail }
    }
  | [] => fun _ => .invariant (.noProgress .topLevel values.span)

/-- Parse a nonempty braced selected-import list. -/
def selectedImports : Parser (NonemptyDelimitedList SelectedImport) := do
  let values ← delimited .leftBrace .rightBrace false selectedImport
    .importDecl .topLevel
  requireSelected values

/-- Require at least one selector in a hiding clause. -/
def requireSelectorNames (values : DelimitedList SelectorName) :
    Parser (NonemptyList SelectorName) :=
  match values.elements with
  | head :: tail => pure { head, tail }
  | [] => fun _ => .invariant (.noProgress .topLevel values.span)

/-- Parse one nonempty `hiding { ... }` clause. -/
def hidingClause : Parser HidingClause := do
  let hidingToken ← contextual .hiding .importDecl
  let values ← delimited .leftBrace .rightBrace false
    (selectorName .importDecl) .importDecl .topLevel
  let names ← requireSelectorNames values
  pure {
    span := SourceSpan.cover hidingToken.span values.span
    value := { names }
  }

/-- Parse an optional selected-import hiding clause. -/
def optionalHiding : Parser (Option HidingClause) := do
  let state ← getState
  if isContextual state .hiding then
    let value ← hidingClause
    pure (some value)
  else
    pure none

end ImportInternals

namespace ImportInternals

/--
Imports uniquely preserve a missing semicolon when another top-level start
immediately follows; every other missing terminator rejects the declaration.
-/
def terminator (lastSpan : SourceSpan) : Parser SourceSpan :=
    fun state =>
  if isSymbol state .semicolon then
    match symbol .semicolon .importDecl state with
    | .ok token next => .ok token.span next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if atTopItemStart state then
    .ok lastSpan (state.emit {
      span := state.currentSpan
      kind := .constraintViolation
        (.trailingSemicolonRequired .importDecl)
    })
  else
    rejectAt state { head := .symbol .semicolon, tail := [] } .importDecl

/-- Finish an import payload with its required or recovered terminator. -/
def finish (start last : SourceSpan)
    (value : ImportDeclValue) : Parser ImportDecl := do
  let endSpan ← terminator last
  pure {
    span := SourceSpan.cover start endSpan
    value
  }

end ImportInternals

namespace ImportInternals

/-- Parse an unqualified module import payload. -/
def plainImport (start : SourceSpan) : Parser ImportDecl := do
  let path ← modulePath .importDecl
  ImportInternals.finish start path.span (.plain path)

/-- Parse a wildcard namespace alias import payload. -/
def namespaceImport (start : SourceSpan) : Parser ImportDecl := do
  let _ ← symbol .star .importDecl
  let _ ← keyword .asKw .importDecl
  let alias ← identifier .importDecl
  let _ ← contextual .from .importDecl
  let path ← modulePath .importDecl
  ImportInternals.finish start path.span (.namespace path alias)

/-- Parse a wildcard import payload with optional hiding. -/
def wildcardImport (start : SourceSpan) : Parser ImportDecl := do
  let _ ← symbol .star .importDecl
  let _ ← contextual .from .importDecl
  let path ← modulePath .importDecl
  let hidden ← optionalHiding
  let last := match hidden with
    | some clause => clause.span
    | none => path.span
  finish start last (.wildcard path hidden)

/-- Parse a selected import payload with optional hiding. -/
def selectiveImport (start : SourceSpan) : Parser ImportDecl := do
  let selection ← selectedImports
  let _ ← contextual .from .importDecl
  let path ← modulePath .importDecl
  let hidden ← optionalHiding
  let last := match hidden with
    | some clause => clause.span
    | none => path.span
  finish start last (.selected selection path hidden)

end ImportInternals

/-- Parse one canonical import declaration. -/
def importDecl : Parser ImportDecl := do
  let importKeyword ← keyword .importKw .importDecl
  let state ← getState
  if isSymbol state .star then
    if state.peekOffsetKind? 1 == some (.keyword .asKw) then
      ImportInternals.namespaceImport importKeyword.span
    else
      ImportInternals.wildcardImport importKeyword.span
  else if isSymbol state .leftBrace then
    ImportInternals.selectiveImport importKeyword.span
  else
    ImportInternals.plainImport importKeyword.span

end Solcore.Syntax.Parser
