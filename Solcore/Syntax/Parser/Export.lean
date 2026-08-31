import Solcore.Syntax.Parser.Delimited
import Solcore.Syntax.Parser.Operator

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

private def exportSelection : Parser ExportSelection := fun state =>
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

private def finishExport (start : SourceSpan)
    (value : ExportDeclValue) : Parser ExportDecl := do
  let semicolon ← symbol .semicolon .exportDecl
  pure {
    span := SourceSpan.cover start semicolon.span
    value
  }

private def localExport (start : SourceSpan) : Parser ExportDecl := do
  let items ← delimited .leftBrace .rightBrace true
    ExportInternals.localExportItem
    .exportDecl .topLevel
  finishExport start (.local items)

private def pathExport (start : SourceSpan) : Parser ExportDecl := do
  let path ← ExportInternals.exportPath
  let state ← getState
  if isSymbol state .dot then
    let _ ← symbol .dot .exportDecl
    let selection ← exportSelection
    finishExport start (.itemsFrom path selection)
  else if isKeyword state .asKw then
    let _ ← keyword .asKw .exportDecl
    let alias ← identifier .exportDecl
    finishExport start (.moduleAs path alias)
  else
    finishExport start (.module path)

/-- Parse one canonical export declaration. -/
def exportDecl : Parser ExportDecl := do
  let exportKeyword ← keyword .exportKw .exportDecl
  let state ← getState
  if isSymbol state .leftBrace then
    localExport exportKeyword.span
  else
    pathExport exportKeyword.span

end Solcore.Syntax.Parser
