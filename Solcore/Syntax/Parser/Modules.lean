import Solcore.Syntax.Parser.State
import Solcore.Syntax.Parser.Diagnostic
import Solcore.Syntax.Foundation
import Solcore.Syntax.Token
import Solcore.Syntax.Parser.Primitive
import Solcore.Syntax.Source
import Solcore.Syntax.Module
import Solcore.Syntax.Parser.Tokens

/-!
Parsers for module paths, imports, exports and pragmas.

Main declarations: `modulePath`, `importDecl`, `exportDecl`, `pragmaDecl`.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.Front.ModulePath
set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Parse a dotted module path with its optional external-package marker. -/
def modulePath (context : ParseContext) : Parser ModulePath := fun state =>
  if isSymbol state .at then
    match symbol .at context state with
    | .ok marker afterMarker =>
        match qualifiedName context .topLevel afterMarker with
        | .ok name next => .ok {
            span := SourceSpan.cover marker.span name.span
            value := {
              externalMarker := some marker.span
              components := name.value.components
            }
          } next
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else
    match qualifiedName context .topLevel state with
    | .ok name next => .ok {
        span := name.span
        value := {
          externalMarker := none
          components := name.value.components
        }
      } next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Import
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Export
set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ExportInternals

/-- Finish an export path without consuming its following selection suffix. -/
def finishExportPath (first last : Identifier)
    (tailRev : List Identifier) (state : State) : Reply QualifiedName :=
  .ok {
    span := SourceSpan.cover first.span last.span
    value := {
      components := { head := first, tail := tailRev.reverse }
    }
  } state

/-- Whether a dot is followed by another ordinary export-path component. -/
def continuesExportPath (state : State) : Bool :=
  isSymbol state .dot &&
    match state.peekOffsetKind? 1 with
    | some (.identifier _) => true
    | _ => false

/-- Consume the remaining identifier components of an export path. -/
def exportPathTail (first : Identifier) :
    Nat → Identifier → List Identifier → State → Reply QualifiedName
  | 0, _, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, last, tailRev, state =>
      if continuesExportPath state then
        match symbol .dot .exportDecl state with
        | .ok _ afterDot =>
            match identifier .exportDecl afterDot with
            | .ok component next =>
                exportPathTail first fuel component
                  (component :: tailRev) next
            | .reject failure next => .reject failure next
            | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        finishExportPath first last tailRev state

/-- Qualified export path that stops before a `.*` or `.{...}` suffix. -/
def exportPath : Parser QualifiedName := fun state =>
  match identifier .exportDecl state with
  | .ok first next =>
      exportPathTail first (next.remainingCount + 1) first [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end ExportInternals

namespace ExportInternals

/-- Convert a parsed constructor list to its required nonempty form. -/
def requireConstructorNames (values : DelimitedList Identifier) :
    Parser (NonemptyList Identifier) :=
  match values.elements with
  | head :: tail => pure { head, tail }
  | [] => fun _ => .invariant (.noProgress .topLevel values.span)

/-- Parse an all-or-named constructor selection following an export name. -/
def constructorSelection : Parser ConstructorSelection := do
  let state ← getState
  if state.peekOffsetKind? 1 == some (.symbol .star) then
    let opening ← symbol .leftParen .exportDecl
    let marker ← symbol .star .exportDecl
    let closing ← symbol .rightParen .exportDecl
    pure {
      span := SourceSpan.cover opening.span closing.span
      value := .all marker.span
    }
  else
    let values ← delimitedNoTrailing .leftParen .rightParen false
      (identifier .exportDecl) .exportDecl .topLevel
    let constructors ← requireConstructorNames values
    pure {
      span := values.span
      value := .named constructors
    }

end ExportInternals

namespace ExportInternals

/-- Parse one wildcard, operator, or identifier export name. -/
def exportName : Parser ExportName := fun state =>
  if isSymbol state .star then
    match symbol .star .exportDecl state with
    | .ok marker next => .ok {
        span := marker.span
        value := .wildcard marker.span
      } next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isSymbol state .leftParen then
    match operatorSelector .exportDecl state with
    | .ok selected next =>
        match selected.value with
        | .operator spelling => .ok {
            span := selected.span
            value := .operator { span := selected.span, value := spelling }
          } next
        | .identifier _ => .invariant
            (.noProgress .topLevel selected.span)
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else
    match identifier .exportDecl state with
    | .ok name afterName =>
        if isSymbol afterName .leftParen then
          match ExportInternals.constructorSelection afterName with
          | .ok constructors next => .ok {
              span := SourceSpan.cover name.span constructors.span
              value := .identifier name (some constructors)
            } next
          | .reject failure next => .reject failure next
          | .invariant error => .invariant error
        else
          .ok {
            span := name.span
            value := .identifier name none
          } afterName
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error

end ExportInternals

namespace ExportInternals

/-- Parse one local export name or qualified module wildcard. -/
def localExportItem : Parser LocalExportItem := fun state =>
  if isIdentifier state && isSymbol
      { state with cursor := state.cursor + 1 } .dot then
    match ExportInternals.exportPath state with
    | .ok path afterPath =>
        match symbol .dot .exportDecl afterPath with
        | .ok _ afterDot =>
            match symbol .star .exportDecl afterDot with
            | .ok marker next => .ok {
                span := SourceSpan.cover path.span marker.span
                value := .moduleWildcard path marker.span
              } next
            | .reject failure next => .reject failure next
            | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else
    match ExportInternals.exportName state with
    | .ok name next => .ok {
        span := name.span
        value := .name name
      } next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error

end ExportInternals

namespace ExportInternals

/-- Parse a wildcard or braced selection following an export module path. -/
def exportSelection : Parser ExportSelection := fun state =>
  if isSymbol state .star then
    match symbol .star .exportDecl state with
    | .ok marker next => .ok {
        span := marker.span
        value := .wildcard marker.span
      } next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else
    match delimited .leftBrace .rightBrace true ExportInternals.exportName
        .exportDecl .topLevel state with
    | .ok items next => .ok {
        span := items.span
        value := .selected items
      } next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error

end ExportInternals

namespace ExportInternals

/-- Terminate an export declaration and attach its leading source span. -/
def finishExport (start : SourceSpan)
    (value : ExportDeclValue) : Parser ExportDecl := do
  let semicolon ← symbol .semicolon .exportDecl
  pure {
    span := SourceSpan.cover start semicolon.span
    value
  }

/-- Parse a braced list of local exports and its declaration terminator. -/
def localExport (start : SourceSpan) : Parser ExportDecl := do
  let items ← delimited .leftBrace .rightBrace true
    ExportInternals.localExportItem
    .exportDecl .topLevel
  finishExport start (.local items)

end ExportInternals

namespace ExportInternals

/-- Parse a module-path export and its optional selection or alias suffix. -/
def pathExport (start : SourceSpan) : Parser ExportDecl := do
  let path ← ExportInternals.exportPath
  let state ← getState
  if isSymbol state .dot then
    let _ ← symbol .dot .exportDecl
    let selection ← ExportInternals.exportSelection
    ExportInternals.finishExport start (.itemsFrom path selection)
  else if isKeyword state .asKw then
    let _ ← keyword .asKw .exportDecl
    let alias ← identifier .exportDecl
    ExportInternals.finishExport start (.moduleAs path alias)
  else
    ExportInternals.finishExport start (.module path)

end ExportInternals

/-- Parse one canonical export declaration. -/
def exportDecl : Parser ExportDecl := do
  let exportKeyword ← keyword .exportKw .exportDecl
  let state ← getState
  if isSymbol state .leftBrace then
    ExportInternals.localExport exportKeyword.span
  else
    ExportInternals.pathExport exportKeyword.span

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Front.Pragma
set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace PragmaInternals

def pragmaItemsTail :
    Nat → List Identifier → State → Reply (List Identifier)
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, itemsRev, state =>
      if isSymbol state .comma then
        match symbol .comma .pragmaDecl state with
        | .ok _ afterComma =>
            if isSymbol afterComma .semicolon then
              .ok itemsRev.reverse afterComma
            else
              match identifier .pragmaDecl afterComma with
              | .ok item next =>
                  pragmaItemsTail fuel (item :: itemsRev) next
              | .reject failure next => .reject failure next
              | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        .ok itemsRev.reverse state

def pragmaItems : Parser (List Identifier) := fun state =>
  if isSymbol state .semicolon then
    .ok [] state
  else
    match identifier .pragmaDecl state with
    | .ok item next =>
        pragmaItemsTail (next.remainingCount + 1) [item] next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error

end PragmaInternals

open PragmaInternals

/-- Parse one canonical provisional pragma declaration. -/
def pragmaDecl : Parser PragmaDecl := do
  let pragmaKeyword ← keyword .pragmaKw .pragmaDecl
  -- The pragma name deliberately omits the ordinary hyphen diagnostic.
  let name ← rawIdentifier .pragmaDecl
  let items ← pragmaItems
  let semicolon ← symbol .semicolon .pragmaDecl
  pure {
    span := SourceSpan.cover pragmaKeyword.span semicolon.span
    value := { name, items }
  }

end Solcore.Syntax.Parser
end
