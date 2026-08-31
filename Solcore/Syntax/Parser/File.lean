import Solcore.Syntax.Parser.Export
import Solcore.Syntax.Parser.Import
import Solcore.Syntax.Parser.Pragma
import Solcore.Syntax.Parser.TopLevel
import Solcore.Syntax.Parser.Trivia
import Solcore.Syntax.Parser.TypeAlias

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def wrapTypeAlias (declaration : TypeAliasDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .typeAlias declaration
}

private def wrapImport (declaration : ImportDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .importDecl declaration
}

private def wrapExport (declaration : ExportDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .exportDecl declaration
}

private def wrapPragma (declaration : PragmaDecl) : TopItem := {
  span := declaration.span
  leadingComments := []
  value := .pragmaDecl declaration
}

/-- Parse the top-level forms implemented by the current vertical slice. -/
private def topItem : Parser TopItem := fun state =>
  if isKeyword state .importKw then
    match importDecl state with
    | .ok declaration next => .ok (wrapImport declaration) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isKeyword state .exportKw then
    match exportDecl state with
    | .ok declaration next => .ok (wrapExport declaration) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isKeyword state .pragmaKw then
    match pragmaDecl state with
    | .ok declaration next => .ok (wrapPragma declaration) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else if isKeyword state .typeKw then
    match typeAlias state with
    | .ok declaration next => .ok (wrapTypeAlias declaration) next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else
    rejectAt state { head := .topItem, tail := [] } .topItem

private def finishRecoveredTopItem (first last : SourceSpan)
    (state : State) : Reply TopItem :=
  let span := SourceSpan.cover first last
  .ok {
    span
    leadingComments := []
    value := .error
  } (state.emit {
    span
    kind := .recovered .topItem
  })

private def recoverTopItemAux (first last : SourceSpan) :
    Nat → State → Reply TopItem
  | 0, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, state =>
      if state.atEnd || atTopItemStart state then
        finishRecoveredTopItem first last state
      else
        match state.advance? with
        | some (token, next) =>
            recoverTopItemAux first token.span fuel next
        | none => finishRecoveredTopItem first last state

private def recoverTopItem (state : State) : Reply TopItem :=
  match state.advance? with
  | some (token, next) =>
      recoverTopItemAux token.span token.span
        (next.remainingCount + 1) next
  | none => rejectAt state { head := .topItem, tail := [] } .topItem

private def parseItems :
    Nat → List TopItem → State → Reply (List TopItem)
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, itemsRev, state =>
      if state.atEnd then
        .ok itemsRev.reverse state
      else
        match topItem state with
        | .ok item next =>
            if next.cursor > state.cursor then
              parseItems fuel (item :: itemsRev) next
            else
              .invariant (.noProgress .topLevel next.currentSpan)
        | .reject failure failedState =>
            let rewound := {
              failedState with
              cursor := state.cursor
            }
            if atTopItemStart state then
              -- Rust recovery also refuses to consume a recognized item start.
              .ok itemsRev.reverse (rewound.emit failure.toDiagnostic)
            else
              -- The enclosing recovery diagnostic replaces its inner failure.
              match recoverTopItem rewound with
              | .ok item next =>
                  parseItems fuel (item :: itemsRev) next
              | .reject recoveryFailure next =>
                  .reject recoveryFailure next
              | .invariant error => .invariant error
        | .invariant error => .invariant error

/-- Parse a complete token window into a source-owned syntax file. -/
def sourceFile (comments : List Comment) : Parser ParsedFile := fun state =>
  match parseItems (state.remainingCount + 1) [] state with
  | .ok items next => .ok {
      source := state.file.id
      span := SourceSpan.fullFile state.file
      items := items.map (attachTopItemComments state.file comments)
      comments
    } next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end Solcore.Syntax.Parser
